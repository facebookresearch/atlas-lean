/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import MathlibExt.NumberTheory.ArithmeticFunction.WeightedDirichletConvolution
import Mathlib.Algebra.Order.Floor.Semifield
import MathlibExt.Algebra.BigOperators.HomogeneousGeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring

/-!
# Weighted summation of Dirichlet convolutions

This module proves the weighted summation formula for the Dirichlet convolution of two
completely multiplicative complex-valued arithmetic functions. It also proves
`sum_dirichletConvolution_mul_eq`: the sum of such a convolution over multiples of `r` equals a
divisor sum weighted by the Möbius function, by a gcd expansion of the convolution at a product.

Reference: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Theorem 1, Equation (8), and Lemma 3, Equation (20).
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

open scoped Classical in
private noncomputable def coprimePart (v : ArithmeticFunction ℂ) (d : ℕ) :
    ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n.Coprime d then v n else 0, by simp⟩

open scoped Classical in
private noncomputable def divisorPart (v : ArithmeticFunction ℂ) (d : ℕ) :
    ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n ∣ d then (μ n : ℂ) * v n else 0, by simp⟩

open scoped Classical in
private theorem sum_moebius_coprime (n d : ℕ) (hn : n ≠ 0) :
    ∑ m ∈ n.divisors with m ∣ d, (μ m : ℂ) = if n.Coprime d then 1 else 0 := by
  have hset : n.divisors.filter (· ∣ d) = (n.gcd d).divisors := by
    ext m
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hn,
      (Nat.gcd_pos_of_pos_left d (Nat.pos_of_ne_zero hn)).ne']
  rw [hset]
  change ∑ m ∈ (n.gcd d).divisors, (μ : ArithmeticFunction ℂ) m =
    if n.Coprime d then 1 else 0
  rw [← coe_mul_zeta_apply]
  by_cases hg : n.gcd d = 1 <;> simp [Nat.Coprime, hg, ArithmeticFunction.one_apply_ne]

open scoped Classical in
private theorem mul_divisorPart {v : ArithmeticFunction ℂ}
    (hv : v.IsCompletelyMultiplicative) (d : ℕ) : v * divisorPart v d = coprimePart v d := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b ↦ v a * divisorPart v d b)]
  change ∑ m ∈ n.divisors, v (n / m) * (if m ∣ d then (μ m : ℂ) * v m else 0) =
    if n.Coprime d then v n else 0
  calc
    _ = v n * ∑ m ∈ n.divisors with m ∣ d, (μ m : ℂ) := by
      rw [mul_sum, sum_filter]
      refine sum_congr rfl fun m hm ↦ ?_
      by_cases hmd : m ∣ d
      · simp only [hmd, ite_true]
        have hvm : v n = v (n / m) * v m := by
          simpa only [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)] using
            hv.map_mul (n / m) m
        rw [hvm]
        ac_rfl
      · simp [hmd]
    _ = _ := by
      rw [sum_moebius_coprime n d hn]
      by_cases hc : n.Coprime d <;> simp [hc]

private theorem product_factors {r j d a : ℕ} (hd : d ∣ r) (ha : a ∣ j) :
    d * (j / a) * ((r / d) * a) = r * j := by
  calc
    _ = (d * (r / d)) * (a * (j / a)) := by ac_rfl
    _ = _ := by rw [Nat.mul_div_cancel' hd, Nat.mul_div_cancel' ha]

private theorem gcd_product_factors {r d a : ℕ} (hd : d ∣ r) (hc : a.Coprime d) :
    r.gcd ((r / d) * a) = r / d := by
  calc
    _ = ((r / d) * d).gcd ((r / d) * a) :=
      congrArg (fun t ↦ t.gcd ((r / d) * a)) (Nat.div_mul_cancel hd).symm
    _ = _ := by rw [Nat.gcd_mul_left, hc.symm.gcd_eq_one, mul_one]

private theorem gcd_factor_eq {r j k b : ℕ} (hr : 0 < r) (hp : k * b = r * j) :
    k * (b / r.gcd b) = (r / r.gcd b) * j := by
  apply Nat.mul_left_cancel (Nat.gcd_pos_of_pos_left b hr)
  calc
    _ = k * (r.gcd b * (b / r.gcd b)) := by ac_rfl
    _ = k * b := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right r b)]
    _ = r * j := hp
    _ = (r.gcd b * (r / r.gcd b)) * j := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left r b)]
    _ = _ := by ac_rfl

private theorem exists_product_factors {r j : ℕ} (hr : 0 < r) (hj : 0 < j)
    {p : ℕ × ℕ} (hp : p ∈ (r * j).divisorsAntidiagonal) :
    ∃ d ∈ r.divisors, ∃ a ∈ j.divisors, a.Coprime d ∧
      (d * (j / a), (r / d) * a) = p := by
  let g := r.gcd p.2
  let d := r / g
  let a := p.2 / g
  have hgd : g ∣ r := Nat.gcd_dvd_left r p.2
  have hd : d ∣ r := Nat.div_dvd_of_dvd hgd
  have hc : a.Coprime d :=
    (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left p.2 hr)).symm
  have heq : p.1 * a = d * j := gcd_factor_eq hr (Nat.mem_divisorsAntidiagonal.mp hp).1
  have ha : a ∣ j := hc.dvd_of_dvd_mul_left (heq ▸ dvd_mul_left a p.1)
  refine ⟨d, Nat.mem_divisors.mpr ⟨hd, hr.ne'⟩,
    a, Nat.mem_divisors.mpr ⟨ha, hj.ne'⟩, hc, Prod.ext ?_ ?_⟩
  · change d * (j / a) = p.1
    apply Nat.mul_right_cancel (Nat.pos_of_dvd_of_pos ha hj)
    calc
      _ = d * ((j / a) * a) := by ac_rfl
      _ = d * j := by rw [Nat.div_mul_cancel ha]
      _ = _ := heq.symm
  · change (r / (r / g)) * (p.2 / g) = p.2
    rw [Nat.div_div_self hgd hr.ne', Nat.mul_div_cancel' (Nat.gcd_dvd_right r p.2)]

private theorem product_factors_injective {r j : ℕ} (hr : 0 < r) {p q : ℕ × ℕ}
    (hp : p.1 ∣ r) (hq : q.1 ∣ r) (hcp : p.2.Coprime p.1) (hcq : q.2.Coprime q.1)
    (h : (p.1 * (j / p.2), (r / p.1) * p.2) =
      (q.1 * (j / q.2), (r / q.1) * q.2)) : p = q := by
  have hg := congrArg (fun t : ℕ × ℕ ↦ r.gcd t.2) h
  change r.gcd ((r / p.1) * p.2) = r.gcd ((r / q.1) * q.2) at hg
  rw [gcd_product_factors hp hcp, gcd_product_factors hq hcq] at hg
  have hd : p.1 = q.1 := by
    calc
      _ = r / (r / p.1) := (Nat.div_div_self hp hr.ne').symm
      _ = r / (r / q.1) := congrArg (r / ·) hg
      _ = _ := Nat.div_div_self hq hr.ne'
  apply Prod.ext hd
  apply Nat.mul_left_cancel (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hq) hr)
  simpa only [hd] using congrArg Prod.snd h

open scoped Classical in
private theorem sum_product_factors {r j : ℕ} (hr : 0 < r) (hj : 0 < j)
    (f : ℕ → ℕ → ℂ) :
    ∑ p ∈ (r * j).divisorsAntidiagonal, f p.1 p.2 =
      ∑ d ∈ r.divisors, ∑ a ∈ j.divisors with a.Coprime d,
        f (d * (j / a)) ((r / d) * a) := by
  symm
  calc
    _ = ∑ p ∈ (r.divisors ×ˢ j.divisors).filter (fun p ↦ p.2.Coprime p.1),
        f (p.1 * (j / p.2)) ((r / p.1) * p.2) := by
      rw [sum_filter, sum_product]
      simp_rw [sum_filter]
    _ = _ := by
      apply sum_nbij (fun p : ℕ × ℕ ↦ (p.1 * (j / p.2), (r / p.1) * p.2))
      · intro p hp
        obtain ⟨⟨hd, ha⟩, -⟩ := mem_filter.mp hp |>.imp_left mem_product.mp
        exact Nat.mem_divisorsAntidiagonal.mpr ⟨product_factors
          (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors ha), (Nat.mul_pos hr hj).ne'⟩
      · intro p hp q hq h
        obtain ⟨⟨hdp, -⟩, hcp⟩ := mem_filter.mp hp |>.imp_left mem_product.mp
        obtain ⟨⟨hdq, -⟩, hcq⟩ := mem_filter.mp hq |>.imp_left mem_product.mp
        exact product_factors_injective hr (Nat.dvd_of_mem_divisors hdp)
          (Nat.dvd_of_mem_divisors hdq) hcp hcq h
      · intro p hp
        obtain ⟨d, hd, a, ha, hc, h⟩ := exists_product_factors hr hj hp
        exact ⟨(d, a), mem_filter.mpr ⟨mem_product.mpr ⟨hd, ha⟩, hc⟩, h⟩
      · exact fun _ _ ↦ rfl

open scoped Classical in
private theorem convolution_product {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    {r j : ℕ} (hr : 0 < r) (hj : 0 < j) :
    (u * v) (r * j) = ∑ d ∈ r.divisors,
      u d * v (r / d) * ((u * v) * divisorPart v d) j := by
  rw [ArithmeticFunction.mul_apply, sum_product_factors hr hj (fun a b ↦ u a * v b)]
  refine sum_congr rfl fun d _ ↦ ?_
  have hf : (u * v) * divisorPart v d = u * coprimePart v d := by
    rw [mul_assoc, mul_divisorPart hv d]
  rw [hf, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b ↦ u a * coprimePart v d b)]
  change ∑ a ∈ j.divisors with a.Coprime d, u (d * (j / a)) * v ((r / d) * a) =
    u d * v (r / d) * ∑ a ∈ j.divisors, u (j / a) *
      (if a.Coprime d then v a else 0)
  rw [sum_filter, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  change (if a.Coprime d then u (d * (j / a)) * v ((r / d) * a) else 0) =
    u d * v (r / d) * (u (j / a) * (if a.Coprime d then v a else 0))
  by_cases hc : a.Coprime d
  · rw [ite_eq_left hc, ite_eq_left hc, hu.map_mul, hv.map_mul]
    ac_rfl
  · simp [hc]

open scoped Classical in
private theorem sum_multiples (f : ℕ → ℂ) (N m : ℕ) (hm : 0 < m) :
    ∑ n ∈ Icc 1 N with m ∣ n, f n = ∑ j ∈ Icc 1 (N / m), f (m * j) := by
  symm
  apply sum_nbij (m * ·)
  · intro j hj
    obtain ⟨hj₀, hjN⟩ := mem_Icc.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hm hj₀,
      by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp hjN⟩,
      dvd_mul_right m j⟩
  · exact (mul_right_injective₀ hm.ne').injOn
  · intro n hn
    obtain ⟨hn, j, rfl⟩ := mem_filter.mp hn
    obtain ⟨hpos, hle⟩ := mem_Icc.mp hn
    refine ⟨j, mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hpos, ?_⟩, rfl⟩
    exact (Nat.le_div_iff_mul_le hm).mpr (Nat.mul_comm _ _ ▸ hle)
  · exact fun _ _ ↦ rfl

open scoped Classical in
private theorem mul_divisorPart_apply (f v : ArithmeticFunction ℂ) (n d : ℕ) :
    (f * divisorPart v d) n =
      ∑ m ∈ n.divisors with m ∣ d, (μ m : ℂ) * v m * f (n / m) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b ↦ f a * divisorPart v d b), sum_filter]
  refine sum_congr rfl fun m _ ↦ ?_
  change f (n / m) * (if m ∣ d then (μ m : ℂ) * v m else 0) =
    if m ∣ d then (μ m : ℂ) * v m * f (n / m) else 0
  by_cases hmd : m ∣ d <;> simp [hmd, mul_comm]

open scoped Classical in
private theorem sum_mul_divisorPart (f v : ArithmeticFunction ℂ) (N d : ℕ) (hd : d ≠ 0) :
    ∑ n ∈ Icc 1 N, (f * divisorPart v d) n =
      ∑ m ∈ d.divisors, (μ m : ℂ) * v m * ∑ j ∈ Icc 1 (N / m), f j := by
  simp_rw [mul_divisorPart_apply]
  calc
    _ = ∑ m ∈ d.divisors, ∑ n ∈ Icc 1 N with m ∣ n,
        (μ m : ℂ) * v m * f (n / m) := by
      apply sum_comm'
      intro n m
      simp only [mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hn, ⟨hmn, -⟩, hmd⟩
        exact ⟨⟨hn, hmn⟩, hmd, hd⟩
      · rintro ⟨⟨hn, hmn⟩, hmd, -⟩
        exact ⟨hn, ⟨hmn, Nat.ne_of_gt (mem_Icc.mp hn).1⟩, hmd⟩
    _ = _ := by
      refine sum_congr rfl fun m hm ↦ ?_
      have hm₀ := Nat.pos_of_mem_divisors hm
      rw [← mul_sum, sum_multiples (fun n ↦ f (n / m)) N m hm₀]
      simp only [Nat.mul_div_cancel_left _ hm₀]

open scoped Classical in
private theorem sum_convolution_multiples {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (r : ℕ) (hr : 0 < r) (x : ℝ) :
    ∑ j ∈ Icc 1 ⌊x / r⌋₊, (u * v) (r * j) =
      ∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
        ∑ j ∈ Icc 1 ⌊x / (m * r)⌋₊, (u * v) j := by
  have hfloor (m : ℕ) : ⌊x / ((m : ℝ) * r)⌋₊ = ⌊x / r⌋₊ / m := by
    rw [mul_comm, ← div_div, Nat.floor_div_natCast]
  simp_rw [hfloor]
  calc
    _ = ∑ j ∈ Icc 1 ⌊x / r⌋₊, ∑ d ∈ r.divisors,
        u d * v (r / d) * ((u * v) * divisorPart v d) j := by
      exact sum_congr rfl fun j hj ↦ convolution_product hu hv hr (mem_Icc.mp hj).1
    _ = ∑ d ∈ r.divisors, u d * v (r / d) *
        ∑ j ∈ Icc 1 ⌊x / r⌋₊, ((u * v) * divisorPart v d) j := by
      rw [sum_comm]
      simp_rw [mul_sum]
    _ = _ := by
      refine sum_congr rfl fun d hd ↦ ?_
      rw [sum_mul_divisorPart (u * v) v ⌊x / r⌋₊ d (Nat.pos_of_mem_divisors hd).ne']

open scoped Classical in
/-- **Weighted summation of Dirichlet convolutions.** Let $u$ and $v$ be completely
multiplicative arithmetic functions with complex values, let $w$ be any arithmetic function with
complex values, let $*$ denote Dirichlet convolution, let $\mu$ be the Möbius function, put
$g = w * \mu$, and for real $y$ put $D(y) = \sum_{1 \le j \le y} (u * v)(j)$. Then for every
real $x$,
$$
\sum_{1 \le j \le x} w(j)\, (u * v)(j) =
\sum_{1 \le r \le x} g(r) \sum_{d \mid r} u(d)\, v(r/d) \sum_{m \mid d} \mu(m)\, v(m)\,
D\left(\frac{x}{mr}\right),
$$
where $r$, $d$ and $m$ run over positive integers.

Both sides vanish for $x < 1$; the source assumes $x \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Theorem 1, Equation (8) (`integers-2024-A75-thm-1`). -/
public theorem weighted_sum_dirichletConvolution_eq {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (w : ArithmeticFunction ℂ) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x⌋₊, w j * (u * v) j =
      ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
        ∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
          ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j := by
  rw [sum_mul_dirichletConvolution_eq_sum_moebius]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [sum_convolution_multiples hu hv r (mem_Icc.mp hr).1 x]

/-- A completely multiplicative complex function takes value `0` or `1` at `1`. -/
private theorem eq_zero_or_one_at_one (u : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) : u 1 = 0 ∨ u 1 = 1 := by
  have h : u 1 = u 1 * u 1 := by simpa using hu 1 1
  have h0 : u 1 * (1 - u 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.mp h').symm

/-- A completely multiplicative function vanishing at `1` is identically zero. -/
private theorem eq_zero_of_one_eq_zero (u : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (h1 : u 1 = 0) (n : ℕ) : u n = 0 := by
  have h := hu n 1
  rw [mul_one, h1, mul_zero] at h
  exact h

/-- The convolution vanishes when its left factor vanishes. -/
private theorem conv_eq_zero_of_left (u v : ArithmeticFunction ℂ)
    (hu0 : ∀ n, u n = 0) (m : ℕ) : (u * v) m = 0 := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_eq_zero fun x _ => by simp [hu0]

/-- The convolution vanishes when its right factor vanishes. -/
private theorem conv_eq_zero_of_right (u v : ArithmeticFunction ℂ)
    (hv0 : ∀ n, v n = 0) (m : ℕ) : (u * v) m = 0 := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_eq_zero fun x _ => by simp [hv0]

/-- A normalized completely multiplicative function sends prime powers to powers. -/
private theorem apply_pow (u : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (h1 : u 1 = 1) (p k : ℕ) :
    u (p ^ k) = u p ^ k := by
  induction k with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ' p k, hu, ih, pow_succ' (u p) k]

/-- Dirichlet convolution as a sum over divisors. -/
private theorem conv_apply (u v : ArithmeticFunction ℂ) (n : ℕ) :
    (u * v) n = ∑ d ∈ n.divisors, u d * v (n / d) := by
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal fun a b => u a * v b

/-- The convolution at a prime power is a homogeneous sum. -/
private theorem conv_prime_pow (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (h1u : u 1 = 1) (h1v : v 1 = 1) (p k : ℕ) (hp : p.Prime) :
    (u * v) (p ^ k) = ∑ j ∈ Finset.range (k + 1), u p ^ j * v p ^ (k - j) := by
  rw [conv_apply u v (p ^ k), Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjk : j ≤ k := by omega
  rw [apply_pow u hu h1u p j, Nat.pow_div hjk hp.pos, apply_pow v hv h1v p (k - j)]

/-- The gcd of two prime powers is the prime power of the minimum. -/
private theorem gcd_prime_pow (p a b : ℕ) (hp : p.Prime) :
    (p ^ a).gcd (p ^ b) = p ^ (min a b) := by
  apply dvd_antisymm
  · obtain ⟨j, hja, hj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left _ _)
    have hjb : p ^ j ∣ p ^ b := by rw [← hj]; exact Nat.gcd_dvd_right _ _
    have hjle : j ≤ min a b :=
      le_min hja ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hjb)
    rw [hj]
    exact pow_dvd_pow p hjle
  · exact Nat.dvd_gcd (pow_dvd_pow p (min_le_left a b)) (pow_dvd_pow p (min_le_right a b))

/-- The Möbius-weighted gcd sum at prime powers matches the homogeneous expansion. -/
private theorem sum_gcd_prime_pow (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (h1u : u 1 = 1) (h1v : v 1 = 1) (p a b : ℕ) (hp : p.Prime) :
    ∑ m ∈ ((p ^ a).gcd (p ^ b)).divisors,
        (μ m : ℂ) * u m * v m * (u * v) (p ^ a / m) * (u * v) (p ^ b / m)
      = (∑ j ∈ Finset.range (a + 1), u p ^ j * v p ^ (a - j)) *
          (∑ i ∈ Finset.range (b + 1), u p ^ i * v p ^ (b - i)) -
        u p * v p * (∑ j ∈ Finset.range a, u p ^ j * v p ^ (a - 1 - j)) *
          (∑ i ∈ Finset.range b, u p ^ i * v p ^ (b - 1 - i)) := by
  have hSa : (u * v) (p ^ a) = ∑ j ∈ Finset.range (a + 1), u p ^ j * v p ^ (a - j) :=
    conv_prime_pow u v hu hv h1u h1v p a hp
  have hSb : (u * v) (p ^ b) = ∑ i ∈ Finset.range (b + 1), u p ^ i * v p ^ (b - i) :=
    conv_prime_pow u v hu hv h1u h1v p b hp
  have hS1 : (μ 1 : ℂ) * u 1 * v 1 * (u * v) (p ^ a / 1) * (u * v) (p ^ b / 1)
      = (∑ j ∈ Finset.range (a + 1), u p ^ j * v p ^ (a - j)) *
        (∑ i ∈ Finset.range (b + 1), u p ^ i * v p ^ (b - i)) := by
    simp [h1u, h1v, hSa, hSb]
  have hvan : ∀ j, 2 ≤ j →
      (μ (p ^ j) : ℂ) * u (p ^ j) * v (p ^ j) *
        (u * v) (p ^ a / p ^ j) * (u * v) (p ^ b / p ^ j) = 0 := by
    intro j hj
    have hμ : μ (p ^ j) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega : j ≠ 0)]
      simp [show j ≠ 1 by omega]
    simp [hμ]
  have hcorr : ∀ (ha : 1 ≤ a) (hb : 1 ≤ b),
      (μ p : ℂ) * u p * v p * (u * v) (p ^ a / p) * (u * v) (p ^ b / p)
      = - (u p * v p * (∑ j ∈ Finset.range a, u p ^ j * v p ^ (a - 1 - j)) *
        (∑ i ∈ Finset.range b, u p ^ i * v p ^ (b - 1 - i))) := by
    intro ha hb
    have hpa : p ^ a / p = p ^ (a - 1) := by
      have h := Nat.pow_div ha hp.pos
      rwa [pow_one] at h
    have hpb : p ^ b / p = p ^ (b - 1) := by
      have h := Nat.pow_div hb hp.pos
      rwa [pow_one] at h
    have hfa : (u * v) (p ^ a / p)
        = ∑ j ∈ Finset.range a, u p ^ j * v p ^ (a - 1 - j) := by
      rw [hpa, conv_prime_pow u v hu hv h1u h1v p (a - 1) hp, Nat.sub_add_cancel ha]
    have hfb : (u * v) (p ^ b / p)
        = ∑ i ∈ Finset.range b, u p ^ i * v p ^ (b - 1 - i) := by
      rw [hpb, conv_prime_pow u v hu hv h1u h1v p (b - 1) hp, Nat.sub_add_cancel hb]
    rw [moebius_apply_prime hp, hfa, hfb]
    push_cast
    ring
  rw [gcd_prime_pow p a b hp, Nat.sum_divisors_prime_pow hp]
  by_cases hmin : min a b = 0
  · have h0 : a = 0 ∨ b = 0 := by omega
    have hT0 : u p * v p * (∑ j ∈ Finset.range a, u p ^ j * v p ^ (a - 1 - j)) *
        (∑ i ∈ Finset.range b, u p ^ i * v p ^ (b - 1 - i)) = 0 := by
      rcases h0 with rfl | rfl <;> simp
    simp only [hmin, zero_add, Finset.sum_range_one, pow_zero, hS1, hT0, sub_zero]
  · have h1le : 1 ≤ min a b := by omega
    have ha : 1 ≤ a := le_trans h1le (min_le_left a b)
    have hb : 1 ≤ b := le_trans h1le (min_le_right a b)
    have hsub : Finset.range 2 ⊆ Finset.range (min a b + 1) :=
      Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)
    have h0 : ∀ j ∈ Finset.range (min a b + 1), j ∉ Finset.range 2 →
        (μ (p ^ j) : ℂ) * u (p ^ j) * v (p ^ j) *
          (u * v) (p ^ a / p ^ j) * (u * v) (p ^ b / p ^ j) = 0 := by
      intro j _ hj2
      exact hvan j (not_lt.mp (by simpa using hj2))
    have hred : (∑ j ∈ Finset.range (min a b + 1),
          (μ (p ^ j) : ℂ) * u (p ^ j) * v (p ^ j) *
            (u * v) (p ^ a / p ^ j) * (u * v) (p ^ b / p ^ j))
        = (∑ j ∈ Finset.range 2,
          (μ (p ^ j) : ℂ) * u (p ^ j) * v (p ^ j) *
            (u * v) (p ^ a / p ^ j) * (u * v) (p ^ b / p ^ j)) :=
      (Finset.sum_subset hsub h0).symm
    have h2 : (∑ j ∈ Finset.range 2,
          (μ (p ^ j) : ℂ) * u (p ^ j) * v (p ^ j) *
            (u * v) (p ^ a / p ^ j) * (u * v) (p ^ b / p ^ j))
        = (μ (p ^ 0) : ℂ) * u (p ^ 0) * v (p ^ 0) *
            (u * v) (p ^ a / p ^ 0) * (u * v) (p ^ b / p ^ 0) +
          (μ (p ^ 1) : ℂ) * u (p ^ 1) * v (p ^ 1) *
            (u * v) (p ^ a / p ^ 1) * (u * v) (p ^ b / p ^ 1) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    rw [hred, h2, pow_zero, pow_one, hS1, hcorr ha hb, sub_eq_add_neg]

/-- Gcd expansion of the convolution at a product of prime powers. -/
private theorem conv_mul_prime_pow (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (h1u : u 1 = 1) (h1v : v 1 = 1) (p a b : ℕ) (hp : p.Prime) :
    (u * v) (p ^ a * p ^ b) = ∑ m ∈ ((p ^ a).gcd (p ^ b)).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (p ^ a / m) * (u * v) (p ^ b / m) := by
  rw [← pow_add, conv_prime_pow u v hu hv h1u h1v p (a + b) hp,
    sum_gcd_prime_pow u v hu hv h1u h1v p a b hp]
  exact sum_pow_mul_pow_add_eq (u p) (v p) a b

/-- A two-variable function splitting over coprime products splits over prime powers. -/
private theorem bimult_prod (F : ℕ → ℕ → ℂ)
    (hmul : ∀ r1 s1 r2 s2 : ℕ, (r1 * s1).Coprime (r2 * s2) →
      F (r1 * r2) (s1 * s2) = F r1 s1 * F r2 s2)
    (h11 : F 1 1 = 1) (T : Finset ℕ) (a b : ℕ → ℕ) :
    (∀ p ∈ T, p.Prime) →
    F (∏ p ∈ T, p ^ a p) (∏ p ∈ T, p ^ b p) = ∏ p ∈ T, F (p ^ a p) (p ^ b p) := by
  induction T using Finset.induction with
  | empty => intro hT; simpa using h11
  | insert p T hpT ih =>
    intro hT
    have hT' : ∀ q ∈ T, q.Prime := fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have hpp : p.Prime := hT p (Finset.mem_insert_self p T)
    have hcop : (p ^ a p * p ^ b p).Coprime
        ((∏ q ∈ T, q ^ a q) * (∏ q ∈ T, q ^ b q)) := by
      rw [← Finset.prod_mul_distrib]
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := by
        rintro rfl
        exact hpT hq
      have hpq : p.Coprime q := (Nat.coprime_primes hpp (hT' q hq)).mpr hne
      have e1 : (p ^ a p).Coprime (q ^ a q * q ^ b q) :=
        Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _ hpq))
          (Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _ hpq))
      have e2 : (p ^ b p).Coprime (q ^ a q * q ^ b q) :=
        Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _ hpq))
          (Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _ hpq))
      exact Nat.Coprime.mul_left e1 e2
    simp only [Finset.prod_insert hpT]
    rw [hmul _ _ _ _ hcop, ih hT']

/-- The convolution at a product splits over coprime products. -/
private theorem bimult_conv_mul (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (h1u : u 1 = 1) (h1v : v 1 = 1) (r1 s1 r2 s2 : ℕ)
    (h : (r1 * s1).Coprime (r2 * s2)) :
    (u * v) ((r1 * r2) * (s1 * s2)) = (u * v) (r1 * s1) * (u * v) (r2 * s2) := by
  have hf : (u * v).IsMultiplicative :=
    (hu.isMultiplicative h1u).mul (hv.isMultiplicative h1v)
  have heq : (r1 * r2) * (s1 * s2) = (r1 * s1) * (r2 * s2) := by ring
  rw [heq]
  exact hf.map_mul_of_coprime h

/-- The gcd splits over coprime products. -/
private theorem gcd_mul_of_coprime (r1 s1 r2 s2 : ℕ) (h : (r1 * s1).Coprime (r2 * s2)) :
    (r1 * r2).gcd (s1 * s2) = (r1.gcd s1) * (r2.gcd s2) := by
  have hr1r2 : r1.Coprime r2 :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right r2 s2)
      (Nat.Coprime.coprime_dvd_left (dvd_mul_right r1 s1) h)
  have hr1s2 : r1.Coprime s2 :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left s2 r2)
      (Nat.Coprime.coprime_dvd_left (dvd_mul_right r1 s1) h)
  have hs1r2 : s1.Coprime r2 :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right r2 s2)
      (Nat.Coprime.coprime_dvd_left (dvd_mul_left s1 r1) h)
  have hs1s2 : s1.Coprime s2 :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left s2 r2)
      (Nat.Coprime.coprime_dvd_left (dvd_mul_left s1 r1) h)
  rw [Nat.Coprime.gcd_mul _ hs1s2, Nat.gcd_comm (r1 * r2) s1,
    Nat.Coprime.gcd_mul _ hr1r2, Nat.gcd_comm (r1 * r2) s2,
    Nat.Coprime.gcd_mul _ hr1r2, hs1r2.gcd_eq_one, hr1s2.symm.gcd_eq_one,
    mul_one, one_mul, Nat.gcd_comm s1 r1, Nat.gcd_comm s2 r2]

/-- A divisor sum over a coprime product splits as a double sum. -/
private theorem sum_divisors_mul (T : ℕ → ℂ) (g1 g2 : ℕ) (h : g1.Coprime g2) :
    ∑ m ∈ (g1 * g2).divisors, T m
      = ∑ m1 ∈ g1.divisors, ∑ m2 ∈ g2.divisors, T (m1 * m2) := by
  have e2 : (∑ m1 ∈ g1.divisors, ∑ m2 ∈ g2.divisors, T (m1 * m2))
      = ∑ x ∈ g1.divisors ×ˢ g2.divisors, T (x.1 * x.2) :=
    (Finset.sum_product _ _ (fun x => T (x.1 * x.2))).symm
  rw [e2]
  symm
  refine Finset.sum_bij (fun a _ => a.1 * a.2) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_product] at ha
    obtain ⟨hm1, hm2⟩ := ha
    have hg1 : g1 ≠ 0 := Nat.ne_zero_of_mem_divisors hm1
    have hg2 : g2 ≠ 0 := Nat.ne_zero_of_mem_divisors hm2
    exact Nat.mem_divisors.mpr
      ⟨mul_dvd_mul (Nat.dvd_of_mem_divisors hm1) (Nat.dvd_of_mem_divisors hm2),
        mul_ne_zero hg1 hg2⟩
  · intro a1 ha1 a2 ha2 heq
    have heq' : a1.1 * a1.2 = a2.1 * a2.2 := heq
    rw [Finset.mem_product] at ha1 ha2
    obtain ⟨hm1, hm2⟩ := ha1
    obtain ⟨hm1', hm2'⟩ := ha2
    have hm1pos : 0 < a1.1 := Nat.pos_of_mem_divisors hm1
    have hc1 : a1.1.Coprime a2.2 :=
      Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hm2')
        (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hm1) h)
    have hdvd : a1.1 ∣ a2.1 * a2.2 := by rw [← heq']; exact dvd_mul_right _ _
    have hle1 : a1.1 ∣ a2.1 := Nat.Coprime.dvd_of_dvd_mul_right hc1 hdvd
    have hc2 : a2.1.Coprime a1.2 :=
      Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hm2)
        (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hm1') h)
    have hdvd' : a2.1 ∣ a1.1 * a1.2 := by rw [heq']; exact dvd_mul_right _ _
    have hle2 : a2.1 ∣ a1.1 := Nat.Coprime.dvd_of_dvd_mul_right hc2 hdvd'
    have heq1 : a1.1 = a2.1 := dvd_antisymm hle1 hle2
    have hm2'pos : 0 < a2.1 := by rw [← heq1]; exact hm1pos
    have heq2 : a1.2 = a2.2 := by
      rw [heq1] at heq'
      exact mul_left_cancel₀ (ne_of_gt hm2'pos) heq'
    exact Prod.ext_iff.mpr ⟨heq1, heq2⟩
  · intro b hb
    have hg : g1 * g2 ≠ 0 := Nat.ne_zero_of_mem_divisors hb
    have hg1 : g1 ≠ 0 := left_ne_zero_of_mul hg
    have hg2 : g2 ≠ 0 := right_ne_zero_of_mul hg
    have hdvd : b ∣ g1 * g2 := Nat.dvd_of_mem_divisors hb
    refine ⟨(b.gcd g1, b.gcd g2), Finset.mk_mem_product ?_ ?_, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right b g1, hg1⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right b g2, hg2⟩
    · change b.gcd g1 * b.gcd g2 = b
      rw [← Nat.Coprime.gcd_mul b h, Nat.gcd_eq_left hdvd]
  · exact fun a _ => rfl

/-- The Möbius-weighted gcd sum splits over coprime products. -/
private theorem bimult_gcd_sum (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (h1u : u 1 = 1) (h1v : v 1 = 1) (r1 s1 r2 s2 : ℕ)
    (h : (r1 * s1).Coprime (r2 * s2)) :
    (∑ m ∈ ((r1 * r2).gcd (s1 * s2)).divisors,
      (μ m : ℂ) * u m * v m * (u * v) ((r1 * r2) / m) * (u * v) ((s1 * s2) / m))
    = (∑ m1 ∈ (r1.gcd s1).divisors,
        (μ m1 : ℂ) * u m1 * v m1 * (u * v) (r1 / m1) * (u * v) (s1 / m1)) *
      (∑ m2 ∈ (r2.gcd s2).divisors,
        (μ m2 : ℂ) * u m2 * v m2 * (u * v) (r2 / m2) * (u * v) (s2 / m2)) := by
  have hf : (u * v).IsMultiplicative :=
    (hu.isMultiplicative h1u).mul (hv.isMultiplicative h1v)
  have hgg : (r1.gcd s1).Coprime (r2.gcd s2) :=
    Nat.Coprime.coprime_dvd_right
      ((Nat.gcd_dvd_left r2 s2).trans (dvd_mul_right r2 s2))
      (Nat.Coprime.coprime_dvd_left
        ((Nat.gcd_dvd_left r1 s1).trans (dvd_mul_right r1 s1)) h)
  rw [gcd_mul_of_coprime r1 s1 r2 s2 h,
    sum_divisors_mul _ _ _ hgg, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m1 hm1 => Finset.sum_congr rfl fun m2 hm2 => ?_
  have hd1 : m1 ∣ r1 := (Nat.dvd_of_mem_divisors hm1).trans (Nat.gcd_dvd_left r1 s1)
  have hd1' : m1 ∣ s1 := (Nat.dvd_of_mem_divisors hm1).trans (Nat.gcd_dvd_right r1 s1)
  have hd2 : m2 ∣ r2 := (Nat.dvd_of_mem_divisors hm2).trans (Nat.gcd_dvd_left r2 s2)
  have hd2' : m2 ∣ s2 := (Nat.dvd_of_mem_divisors hm2).trans (Nat.gcd_dvd_right r2 s2)
  have hm12 : m1.Coprime m2 :=
    Nat.Coprime.coprime_dvd_right (hd2.trans (dvd_mul_right r2 s2))
      (Nat.Coprime.coprime_dvd_left (hd1.trans (dvd_mul_right r1 s1)) h)
  have hμ : μ (m1 * m2) = μ m1 * μ m2 :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hm12
  have hr : (r1 * r2) / (m1 * m2) = (r1 / m1) * (r2 / m2) :=
    (Nat.div_mul_div_comm hd1 hd2).symm
  have hs : (s1 * s2) / (m1 * m2) = (s1 / m1) * (s2 / m2) :=
    (Nat.div_mul_div_comm hd1' hd2').symm
  have hcr : (r1 / m1).Coprime (r2 / m2) :=
    Nat.Coprime.coprime_dvd_right ((Nat.div_dvd_of_dvd hd2).trans (dvd_mul_right r2 s2))
      (Nat.Coprime.coprime_dvd_left ((Nat.div_dvd_of_dvd hd1).trans (dvd_mul_right r1 s1)) h)
  have hcs : (s1 / m1).Coprime (s2 / m2) :=
    Nat.Coprime.coprime_dvd_right ((Nat.div_dvd_of_dvd hd2').trans (dvd_mul_left s2 r2))
      (Nat.Coprime.coprime_dvd_left ((Nat.div_dvd_of_dvd hd1').trans (dvd_mul_left s1 r1)) h)
  have hfr : (u * v) ((r1 * r2) / (m1 * m2))
      = (u * v) (r1 / m1) * (u * v) (r2 / m2) := by
    rw [hr]
    exact hf.map_mul_of_coprime hcr
  have hfs : (u * v) ((s1 * s2) / (m1 * m2))
      = (u * v) (s1 / m1) * (u * v) (s2 / m2) := by
    rw [hs]
    exact hf.map_mul_of_coprime hcs
  rw [hμ, hu m1 m2, hv m1 m2, hfr, hfs]
  push_cast
  ring

/-- The convolution at `(1, 1)` is one. -/
private theorem conv_one_one (u v : ArithmeticFunction ℂ) (h1u : u 1 = 1) (h1v : v 1 = 1) :
    (u * v) (1 * 1) = 1 := by
  rw [mul_one, ArithmeticFunction.mul_apply_one, h1u, h1v, mul_one]

/-- The gcd sum at `(1, 1)` is one. -/
private theorem gcd_sum_one_one (u v : ArithmeticFunction ℂ) (h1u : u 1 = 1) (h1v : v 1 = 1) :
    (∑ m ∈ ((1 : ℕ).gcd 1).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (1 / m) * (u * v) (1 / m)) = 1 := by
  have hgcd : (1 : ℕ).gcd 1 = 1 := by decide
  rw [hgcd, Nat.divisors_one, Finset.sum_singleton]
  simp [h1u, h1v]

/-- Gcd expansion of the convolution in the normalized case. -/
private theorem conv_mul_eq_gcd_sum_nrm (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (h1u : u 1 = 1) (h1v : v 1 = 1) (r s : ℕ) :
    (u * v) (r * s) = ∑ m ∈ (r.gcd s).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (s / m) := by
  by_cases hr : r = 0
  · subst hr
    rw [zero_mul, ArithmeticFunction.map_zero]
    exact (Finset.sum_eq_zero fun m _ => by simp [Nat.zero_div, ArithmeticFunction.map_zero]).symm
  · by_cases hs : s = 0
    · subst hs
      rw [mul_zero, ArithmeticFunction.map_zero]
      exact (Finset.sum_eq_zero fun m _ => by simp [Nat.zero_div, ArithmeticFunction.map_zero]).symm
    · set P := (r * s).primeFactors with hPdef
      have hP : ∀ p ∈ P, p.Prime := by
        intro p hp
        rw [hPdef] at hp
        exact Nat.prime_of_mem_primeFactors hp
      have hrw : r = ∏ p ∈ P, p ^ r.factorization p := by
        rw [hPdef]
        conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hr]
        refine Finset.prod_subset ?_ fun p hp hpr => ?_
        · intro p hpmem
          rw [Nat.mem_primeFactors] at hpmem ⊢
          obtain ⟨hprime, hdvd, _⟩ := hpmem
          exact ⟨hprime, dvd_mul_of_dvd_left hdvd s, mul_ne_zero hr hs⟩
        · have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hndvd : ¬ p ∣ r := fun hdvd =>
            hpr (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hr⟩)
          rw [Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
      have hsw : s = ∏ p ∈ P, p ^ s.factorization p := by
        rw [hPdef]
        conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hs]
        refine Finset.prod_subset ?_ fun p hp hpr => ?_
        · intro p hpmem
          rw [Nat.mem_primeFactors] at hpmem ⊢
          obtain ⟨hprime, hdvd, _⟩ := hpmem
          exact ⟨hprime, dvd_mul_of_dvd_right hdvd r, mul_ne_zero hr hs⟩
        · have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
          have hndvd : ¬ p ∣ s := fun hdvd =>
            hpr (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hs⟩)
          rw [Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
      have hF : (u * v) ((∏ p ∈ P, p ^ r.factorization p) *
          (∏ p ∈ P, p ^ s.factorization p))
          = ∏ p ∈ P, (u * v) (p ^ r.factorization p * p ^ s.factorization p) :=
        bimult_prod (fun r s => (u * v) (r * s)) (bimult_conv_mul u v hu hv h1u h1v)
          (conv_one_one u v h1u h1v) _ _ _ hP
      have hG : (∑ m ∈ ((∏ p ∈ P, p ^ r.factorization p).gcd
            (∏ p ∈ P, p ^ s.factorization p)).divisors,
          (μ m : ℂ) * u m * v m *
            (u * v) ((∏ p ∈ P, p ^ r.factorization p) / m) *
            (u * v) ((∏ p ∈ P, p ^ s.factorization p) / m))
          = ∏ p ∈ P, (∑ m ∈ ((p ^ r.factorization p).gcd
            (p ^ s.factorization p)).divisors,
            (μ m : ℂ) * u m * v m * (u * v) (p ^ r.factorization p / m) *
              (u * v) (p ^ s.factorization p / m)) :=
        bimult_prod (fun r s => ∑ m ∈ (r.gcd s).divisors,
            (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (s / m))
          (bimult_gcd_sum u v hu hv h1u h1v) (gcd_sum_one_one u v h1u h1v) _ _ _ hP
      rw [hrw, hsw, hF, hG]
      exact Finset.prod_congr rfl fun p hp =>
        conv_mul_prime_pow u v hu hv h1u h1v p _ _ (hP p hp)

/-- Gcd expansion of the convolution at a product. -/
private theorem conv_mul_eq_gcd_sum (u v : ArithmeticFunction ℂ)
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) (r s : ℕ) :
    (u * v) (r * s) = ∑ m ∈ (r.gcd s).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (s / m) := by
  rcases eq_zero_or_one_at_one u hu with h1u | h1u
  · have hu0 : ∀ n, u n = 0 := eq_zero_of_one_eq_zero u hu h1u
    rw [conv_eq_zero_of_left u v hu0 (r * s)]
    exact (Finset.sum_eq_zero fun m _ => by simp [hu0]).symm
  · rcases eq_zero_or_one_at_one v hv with h1v | h1v
    · have hv0 : ∀ n, v n = 0 := eq_zero_of_one_eq_zero v hv h1v
      rw [conv_eq_zero_of_right u v hv0 (r * s)]
      exact (Finset.sum_eq_zero fun m _ => by simp [hv0]).symm
    · exact conv_mul_eq_gcd_sum_nrm u v hu hv h1u h1v r s

/-- Summing the gcd expansion over an interval swaps to a divisor sum. -/
private theorem sum_gcd_swap (u v : ArithmeticFunction ℂ) (r N : ℕ) (hr : r ≠ 0) :
    (∑ j ∈ Finset.Icc 1 N, ∑ m ∈ (r.gcd j).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (j / m))
    = ∑ m ∈ r.divisors, ∑ t ∈ Finset.Icc 1 (N / m),
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) t := by
  have e1 : (∑ j ∈ Finset.Icc 1 N, ∑ m ∈ (r.gcd j).divisors,
        (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (j / m))
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun j => (r.gcd j).divisors),
        (μ x.2 : ℂ) * u x.2 * v x.2 * (u * v) (r / x.2) * (u * v) (x.1 / x.2) :=
    (Finset.sum_sigma (Finset.Icc 1 N) (fun j => (r.gcd j).divisors)
      (fun x => (μ x.2 : ℂ) * u x.2 * v x.2 * (u * v) (r / x.2) *
        (u * v) (x.1 / x.2))).symm
  have e2 : (∑ m ∈ r.divisors, ∑ t ∈ Finset.Icc 1 (N / m),
        (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) t)
      = ∑ x ∈ r.divisors.sigma (fun m => Finset.Icc 1 (N / m)),
        (μ x.1 : ℂ) * u x.1 * v x.1 * (u * v) (r / x.1) * (u * v) x.2 :=
    (Finset.sum_sigma r.divisors (fun m => Finset.Icc 1 (N / m))
      (fun x => (μ x.1 : ℂ) * u x.1 * v x.1 * (u * v) (r / x.1) * (u * v) x.2)).symm
  rw [e1, e2]
  refine Finset.sum_bij (fun a _ => (⟨a.2, a.1 / a.2⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_sigma] at ha
    obtain ⟨hj, hm⟩ := ha
    rw [Finset.mem_Icc] at hj
    obtain ⟨hj1, hjN⟩ := hj
    have hmpos : 0 < a.2 := Nat.pos_of_mem_divisors hm
    have hmr : a.2 ∣ r := (Nat.dvd_of_mem_divisors hm).trans (Nat.gcd_dvd_left r a.1)
    have hmj : a.2 ∣ a.1 := (Nat.dvd_of_mem_divisors hm).trans (Nat.gcd_dvd_right r a.1)
    rw [Finset.mem_sigma]
    refine ⟨Nat.mem_divisors.mpr ⟨hmr, hr⟩, ?_⟩
    rw [Finset.mem_Icc]
    refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega : 0 < a.1) hmj) hmpos, ?_⟩
    exact Nat.div_le_div_right hjN
  · intro a1 ha1 a2 ha2 heq
    have heq' : (⟨a1.2, a1.1 / a1.2⟩ : Sigma fun _ : ℕ => ℕ) = ⟨a2.2, a2.1 / a2.2⟩ := heq
    rw [Finset.mem_sigma] at ha1 ha2
    obtain ⟨-, hm1⟩ := ha1
    obtain ⟨-, hm2⟩ := ha2
    have hmj1 : a1.2 ∣ a1.1 :=
      (Nat.dvd_of_mem_divisors hm1).trans (Nat.gcd_dvd_right r a1.1)
    have hmj2 : a2.2 ∣ a2.1 :=
      (Nat.dvd_of_mem_divisors hm2).trans (Nat.gcd_dvd_right r a2.1)
    have e1 : a1.2 = a2.2 := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.1) heq'
    have e2' : a1.1 / a1.2 = a2.1 / a2.2 :=
      congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.2) heq'
    have ea1 : a1.1 = a2.1 := by
      have h1 := Nat.div_mul_cancel hmj1
      have h2 := Nat.div_mul_cancel hmj2
      rw [e1] at h1 e2'
      rw [← h1, e2', h2]
    have eta1 : a1 = ⟨a1.1, a1.2⟩ := rfl
    have eta2 : a2 = ⟨a2.1, a2.2⟩ := rfl
    rw [eta1, eta2, ea1, e1]
  · intro b hb
    rw [Finset.mem_sigma] at hb
    obtain ⟨hm, ht⟩ := hb
    rw [Finset.mem_Icc] at ht
    obtain ⟨ht1, htN⟩ := ht
    have hmpos : 0 < b.1 := Nat.pos_of_mem_divisors hm
    have hmr : b.1 ∣ r := Nat.dvd_of_mem_divisors hm
    have htpos : 0 < b.2 := by omega
    have hmt : 0 < b.1 * b.2 := Nat.mul_pos hmpos htpos
    refine ⟨⟨b.1 * b.2, b.1⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨hmt, ?_⟩
      have hle : b.2 * b.1 ≤ N := (Nat.le_div_iff_mul_le hmpos).mp htN
      rwa [mul_comm] at hle
    · refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
      · exact Nat.dvd_gcd hmr (dvd_mul_right b.1 b.2)
      · exact ne_of_gt (Nat.gcd_pos_of_pos_right r hmt)
    · change (⟨b.1, (b.1 * b.2) / b.1⟩ : Sigma fun _ : ℕ => ℕ) = b
      rw [Nat.mul_div_cancel_left _ hmpos]
  · exact fun a _ => rfl

/-- Reindexing a double divisor sum by the product. -/
private theorem sum_divisors_reindex (u v : ArithmeticFunction ℂ) (r : ℕ) (D : ℕ → ℂ) :
    (∑ m ∈ r.divisors, ∑ d' ∈ (r / m).divisors,
      (μ m : ℂ) * u m * v m * (u d' * v ((r / m) / d')) * D m)
    = ∑ d ∈ r.divisors, ∑ m ∈ d.divisors,
      (μ m : ℂ) * u m * v m * (u (d / m) * v ((r / m) / (d / m))) * D m := by
  have e1 : (∑ m ∈ r.divisors, ∑ d' ∈ (r / m).divisors,
        (μ m : ℂ) * u m * v m * (u d' * v ((r / m) / d')) * D m)
      = ∑ x ∈ r.divisors.sigma (fun m => (r / m).divisors),
        (μ x.1 : ℂ) * u x.1 * v x.1 * (u x.2 * v ((r / x.1) / x.2)) * D x.1 :=
    (Finset.sum_sigma r.divisors (fun m => (r / m).divisors)
      (fun x => (μ x.1 : ℂ) * u x.1 * v x.1 * (u x.2 * v ((r / x.1) / x.2)) * D x.1)).symm
  have e2 : (∑ d ∈ r.divisors, ∑ m ∈ d.divisors,
        (μ m : ℂ) * u m * v m * (u (d / m) * v ((r / m) / (d / m))) * D m)
      = ∑ x ∈ r.divisors.sigma (fun d => d.divisors),
        (μ x.2 : ℂ) * u x.2 * v x.2 * (u (x.1 / x.2) * v ((r / x.2) / (x.1 / x.2))) * D x.2 :=
    (Finset.sum_sigma r.divisors (fun d => d.divisors)
      (fun x => (μ x.2 : ℂ) * u x.2 * v x.2 * (u (x.1 / x.2) * v ((r / x.2) / (x.1 / x.2))) *
        D x.2)).symm
  rw [e1, e2]
  refine Finset.sum_bij (fun a _ => (⟨a.1 * a.2, a.1⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_sigma] at ha
    obtain ⟨hm, hd'⟩ := ha
    have hmpos : 0 < a.1 := Nat.pos_of_mem_divisors hm
    have hd'pos : 0 < a.2 := Nat.pos_of_mem_divisors hd'
    have hmr : a.1 ∣ r := Nat.dvd_of_mem_divisors hm
    have hr : r ≠ 0 := Nat.ne_zero_of_mem_divisors hm
    have hd'r : a.2 ∣ r / a.1 := Nat.dvd_of_mem_divisors hd'
    have hdmul : a.1 * a.2 ∣ r := by
      have h1 : a.1 * a.2 ∣ a.1 * (r / a.1) := mul_dvd_mul dvd_rfl hd'r
      have h2 : a.1 * (r / a.1) = r := by rw [mul_comm]; exact Nat.div_mul_cancel hmr
      rwa [h2] at h1
    have hdpos : 0 < a.1 * a.2 := Nat.mul_pos hmpos hd'pos
    rw [Finset.mem_sigma]
    refine ⟨Nat.mem_divisors.mpr ⟨hdmul, hr⟩, Nat.mem_divisors.mpr ⟨?_, ?_⟩⟩
    · exact dvd_mul_right a.1 a.2
    · exact ne_of_gt hdpos
  · intro a1 ha1 a2 ha2 heq
    have heq' : (⟨a1.1 * a1.2, a1.1⟩ : Sigma fun _ : ℕ => ℕ) = ⟨a2.1 * a2.2, a2.1⟩ := heq
    have e2 : a1.1 = a2.1 := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.2) heq'
    have e1 : a1.1 * a1.2 = a2.1 * a2.2 :=
      congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.1) heq'
    rw [Finset.mem_sigma] at ha1
    obtain ⟨hm1, -⟩ := ha1
    have hm1pos : 0 < a1.1 := Nat.pos_of_mem_divisors hm1
    have hm2pos : 0 < a2.1 := by rw [← e2]; exact hm1pos
    have ed2 : a1.2 = a2.2 := by
      rw [e2] at e1
      exact mul_left_cancel₀ (ne_of_gt hm2pos) e1
    have eta1 : a1 = ⟨a1.1, a1.2⟩ := rfl
    have eta2 : a2 = ⟨a2.1, a2.2⟩ := rfl
    rw [eta1, eta2, e2, ed2]
  · intro b hb
    rw [Finset.mem_sigma] at hb
    obtain ⟨hd, hm⟩ := hb
    have hmpos : 0 < b.2 := Nat.pos_of_mem_divisors hm
    have hmd : b.2 ∣ b.1 := Nat.dvd_of_mem_divisors hm
    have hdr : b.1 ∣ r := Nat.dvd_of_mem_divisors hd
    have hmr : b.2 ∣ r := hmd.trans hdr
    have hr : r ≠ 0 := Nat.ne_zero_of_mem_divisors hd
    have hrmpos : 0 < r / b.2 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hmr) hmpos
    refine ⟨⟨b.2, b.1 / b.2⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨hmr, hr⟩
    · refine Nat.mem_divisors.mpr ⟨?_, ne_of_gt hrmpos⟩
      exact Nat.div_dvd_div hmd hdr
    · change (⟨b.2 * (b.1 / b.2), b.2⟩ : Sigma fun _ : ℕ => ℕ) = b
      have hdm : b.2 * (b.1 / b.2) = b.1 := by rw [mul_comm]; exact Nat.div_mul_cancel hmd
      rw [hdm]
  · intro a ha
    rw [Finset.mem_sigma] at ha
    obtain ⟨hm, -⟩ := ha
    have hmpos : 0 < a.1 := Nat.pos_of_mem_divisors hm
    change (μ a.1 : ℂ) * u a.1 * v a.1 * (u a.2 * v ((r / a.1) / a.2)) * D a.1
      = (μ a.1 : ℂ) * u a.1 * v a.1 *
        (u ((a.1 * a.2) / a.1) * v ((r / a.1) / ((a.1 * a.2) / a.1))) * D a.1
    rw [Nat.mul_div_cancel_left _ hmpos]

/-- **Sums of a Dirichlet convolution over multiples of $r$.** Let $u$ and $v$ be completely
multiplicative arithmetic functions with complex values, let $u * v$ be their Dirichlet
convolution, let $\mu$ be the Möbius function, and for real $y$ put
$D(y) = \sum_{1 \le j \le y} (u * v)(j)$. Then for every natural number $r$ and every real $x$,
$$
\sum_{1 \le j \le x/r} (u * v)(rj) =
\sum_{d \mid r} u(d)\, v(r/d) \sum_{m \mid d} \mu(m)\, v(m)\, D\left(\frac{x}{mr}\right),
$$
where $d$ and $m$ run over positive divisors and $x/0 = 0$, so both sides vanish for $r = 0$.

Both sides also vanish for $x < 1$; the source assumes $r \ge 1$ and $x \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 3, Equation (20) (`integers-2024-A75-lem-3`). -/
public theorem sum_dirichletConvolution_mul_eq {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) (r : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, (u * v) (r * j) =
      ∑ d ∈ r.divisors, u d * v (r / d) * ∑ m ∈ d.divisors, (μ m : ℂ) * v m *
        ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j
    := by
  by_cases hr : r = 0
  · subst hr
    rw [Nat.cast_zero, div_zero, Nat.floor_zero,
      Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by decide), Nat.divisors_zero,
      Finset.sum_empty, Finset.sum_empty]
  · trans ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, ∑ m ∈ (r.gcd j).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (j / m)
    · exact Finset.sum_congr rfl fun j _ => conv_mul_eq_gcd_sum u v hu hv r j
    trans ∑ m ∈ r.divisors, ∑ t ∈ Finset.Icc 1 (⌊x / r⌋₊ / m),
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) t
    · exact sum_gcd_swap u v r ⌊x / r⌋₊ hr
    trans ∑ m ∈ r.divisors, (μ m : ℂ) * u m * v m * (u * v) (r / m) *
      ∑ t ∈ Finset.Icc 1 (⌊x / r⌋₊ / m), (u * v) t
    · refine Finset.sum_congr rfl fun m _ => ?_
      exact (Finset.mul_sum _ _ _).symm
    trans ∑ m ∈ r.divisors, (μ m : ℂ) * u m * v m * (u * v) (r / m) *
      ∑ t ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) t
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hfloor : ⌊x / r⌋₊ / m = ⌊x / (m * r)⌋₊ := by
        have heq : x / ((m : ℝ) * (r : ℝ)) = (x / (r : ℝ)) / (m : ℝ) := by
          rw [div_div, mul_comm (m : ℝ) (r : ℝ)]
        rw [heq, Nat.floor_div_natCast (x / r) m]
      rw [hfloor]
    trans ∑ m ∈ r.divisors, ∑ d' ∈ (r / m).divisors,
      (μ m : ℂ) * u m * v m * (u d' * v ((r / m) / d')) *
        ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [conv_apply u v (r / m),
        Finset.mul_sum ((r / m).divisors) (fun d' => u d' * v ((r / m) / d')) _,
        Finset.sum_mul]
    trans ∑ d ∈ r.divisors, ∑ m ∈ d.divisors,
      (μ m : ℂ) * u m * v m * (u (d / m) * v ((r / m) / (d / m))) *
        ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j
    · exact sum_divisors_reindex u v r
        (fun m => ∑ j ∈ Finset.Icc 1 ⌊x / (m * r)⌋₊, (u * v) j)
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmd : m ∣ d := Nat.dvd_of_mem_divisors hm
      have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
      have hdm : m * (d / m) = d := by rw [mul_comm]; exact Nat.div_mul_cancel hmd
      have hu_eq : u d = u m * u (d / m) := by rw [← hu m (d / m), hdm]
      have hdiv : (r / m) / (d / m) = r / d := by rw [Nat.div_div_eq_div_mul, hdm]
      rw [hdiv, hu_eq]
      ring

end MetaMathlibExt

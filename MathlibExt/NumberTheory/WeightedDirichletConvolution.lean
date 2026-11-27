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

/-!
# Weighted summation of Dirichlet convolutions

This module proves the weighted summation formula for the Dirichlet convolution of two
completely multiplicative complex-valued arithmetic functions. It also proves
`sum_dirichletConvolution_mul_eq`: the sum of such a convolution over multiples of `r` equals a
divisor sum weighted by the Möbius function.

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

/-- **Sums of a Dirichlet convolution over multiples of $r$.** Let $u$ and $v$ be completely
multiplicative arithmetic functions with complex values, let $u * v$ be their Dirichlet
convolution, let $\mu$ be the Möbius function, and for real $y$ put
$D(y) = \sum_{1 \le j \le y} (u * v)(j)$. Then for every natural number $r$ and every real $x$,
$$
\sum_{1 \le j \le x/r} (u * v)(rj) =
\sum_{d \mid r} u(d)\, v(r/d) \sum_{m \mid d} \mu(m)\, v(m)\, D\left(\frac{x}{mr}\right).
$$
For $r>0$, the divisor sums run over positive divisors. For $r=0$, the outer divisor sum is
empty by convention, and the left sum is empty because $x/0=0$.

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
  · exact sum_convolution_multiples hu hv r (Nat.pos_of_ne_zero hr) x

end MetaMathlibExt

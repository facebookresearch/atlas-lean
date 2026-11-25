/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import MathlibExt.Algebra.BigOperators.HomogeneousGeomSum

/-!
# Weighted sums of Dirichlet convolutions

Möbius inversion expresses a weighted sum of a Dirichlet convolution as a sum over multiples.
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- **Möbius expansion of weighted sums of a Dirichlet convolution.** Let $w$, $u$ and $v$ be
arithmetic functions with complex values, let $*$ denote Dirichlet convolution, let $\mu$ be the
Möbius function and put $g = w * \mu$. Then for every real $x$,
$$
\sum_{1 \le j \le x} w(j)\, (u * v)(j) =
\sum_{1 \le r \le x} g(r) \sum_{1 \le j \le x/r} (u * v)(rj),
$$
where $j$ and $r$ run over positive integers.

Both sides vanish for $x < 1$; the source assumes $x \ge 1$.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 4 (`integers-2024-A75-lem-4`). -/
public theorem sum_mul_dirichletConvolution_eq_sum_moebius (w u v : ArithmeticFunction ℂ)
    (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 ⌊x⌋₊, w j * (u * v) j =
      ∑ r ∈ Finset.Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
        ∑ j ∈ Finset.Icc 1 ⌊x / r⌋₊, (u * v) (r * j) := by
  let g := w * (μ : ArithmeticFunction ℂ)
  let N := ⌊x⌋₊
  have hw (n : ℕ) : w n = ∑ r ∈ n.divisors, g r := by
    rw [← coe_mul_zeta_apply]
    simp [g, mul_assoc]
  simp_rw [Nat.floor_div_natCast]
  change ∑ n ∈ Icc 1 N, w n * (u * v) n =
    ∑ r ∈ Icc 1 N, g r * ∑ j ∈ Icc 1 (N / r), (u * v) (r * j)
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ r ∈ n.divisors, g r * (u * v) n := by
      exact sum_congr rfl fun n _ ↦ by rw [hw, sum_mul]
    _ = ∑ r ∈ Icc 1 N, ∑ n ∈ Icc 1 N with r ∣ n, g r * (u * v) n := by
      apply sum_comm'
      intro n r
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨hn, hd, -⟩
        exact ⟨⟨hn, hd⟩, Nat.pos_of_dvd_of_pos hd hn.1, (Nat.le_of_dvd hn.1 hd).trans hn.2⟩
      · rintro ⟨⟨hn, hd⟩, -⟩
        exact ⟨hn, hd, Nat.ne_of_gt hn.1⟩
    _ = _ := by
      refine sum_congr rfl fun r hr ↦ ?_
      have hr₀ : 0 < r := (mem_Icc.mp hr).1
      rw [← mul_sum]
      congr 1
      symm
      apply sum_nbij (r * ·)
      · intro j hj
        obtain ⟨hj₀, hjN⟩ := mem_Icc.mp hj
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hr₀ hj₀,
          by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr₀).mp hjN⟩, dvd_mul_right r j⟩
      · exact (mul_right_injective₀ hr₀.ne').injOn
      · intro n hn
        obtain ⟨hn, j, rfl⟩ := mem_filter.mp hn
        obtain ⟨hpos, hle⟩ := mem_Icc.mp hn
        refine ⟨j, mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hpos, ?_⟩, rfl⟩
        exact (Nat.le_div_iff_mul_le hr₀).mpr (Nat.mul_comm _ _ ▸ hle)
      · exact fun _ _ ↦ rfl

private theorem completelyMultiplicative_eq_zero_or_map_one {f : ArithmeticFunction ℂ}
    (hf : f.IsCompletelyMultiplicative) : f = 0 ∨ f 1 = 1 := by
  have h := hf.map_mul 1 1
  rw [Nat.mul_one] at h
  have h' : f 1 * (f 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · left
    ext n
    simpa [h0] using hf.map_mul 1 n
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem sum_divisors_coprime_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.Coprime b) (F : ℕ → ℂ) :
    ∑ d ∈ (a * b).divisors, F d = ∑ m ∈ a.divisors, ∑ n ∈ b.divisors, F (m * n) := by
  have recover {m n : ℕ} (hm : m ∣ a) (hn : n ∣ b) :
      (m * n).gcd a = m ∧ (m * n).gcd b = n := by
    rw [(hab.symm.of_dvd_left hn).gcd_mul_right_cancel,
      (hab.of_dvd_left hm).gcd_mul_left_cancel]
    exact ⟨Nat.gcd_eq_left_iff_dvd.mpr hm, Nat.gcd_eq_left_iff_dvd.mpr hn⟩
  rw [← sum_product a.divisors b.divisors (fun z : ℕ × ℕ ↦ F (z.1 * z.2))]
  symm
  refine sum_nbij (fun z : ℕ × ℕ ↦ z.1 * z.2) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro z hz
    obtain ⟨hm, hn⟩ := mem_product.mp hz
    exact Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul (Nat.mem_divisors.mp hm).1 (Nat.mem_divisors.mp hn).1, mul_ne_zero ha hb⟩
  · intro x hx y hy hxy
    obtain ⟨hx₁, hx₂⟩ := mem_product.mp hx
    obtain ⟨hy₁, hy₂⟩ := mem_product.mp hy
    have hx' := recover (Nat.mem_divisors.mp hx₁).1 (Nat.mem_divisors.mp hx₂).1
    have hy' := recover (Nat.mem_divisors.mp hy₁).1 (Nat.mem_divisors.mp hy₂).1
    change x.1 * x.2 = y.1 * y.2 at hxy
    rw [hxy] at hx'
    exact Prod.ext (hx'.1.symm.trans hy'.1) (hx'.2.symm.trans hy'.2)
  · intro d hd
    refine ⟨(d.gcd a, d.gcd b), mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, ha⟩
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hb⟩
    · exact (hab.gcd_mul d).symm.trans (Nat.gcd_eq_left_iff_dvd.mpr (Nat.mem_divisors.mp hd).1)

private noncomputable def gcdConvolutionSum (u v : ArithmeticFunction ℂ) (r s : ℕ) : ℂ :=
  ∑ m ∈ (Nat.gcd r s).divisors,
    (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (s / m)

-- The gcd sum separates into two sums when the two blocks have disjoint prime support.
private theorem gcdConvolutionSum_mul {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (hconv : (u * v).IsMultiplicative) {r₁ r₂ s₁ s₂ : ℕ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hc : (r₁ * s₁).Coprime (r₂ * s₂)) :
    gcdConvolutionSum u v (r₁ * r₂) (s₁ * s₂) =
      gcdConvolutionSum u v r₁ s₁ * gcdConvolutionSum u v r₂ s₂ := by
  have hrr : r₁.Coprime r₂ :=
    (hc.of_dvd_left (dvd_mul_right _ _)).of_dvd_right (dvd_mul_right _ _)
  have hss : s₁.Coprime s₂ :=
    (hc.of_dvd_left (dvd_mul_left _ _)).of_dvd_right (dvd_mul_left _ _)
  have hcross₁ : r₁.Coprime s₂ :=
    (hc.of_dvd_left (dvd_mul_right _ _)).of_dvd_right (dvd_mul_left _ _)
  have hcross₂ : r₂.Coprime s₁ :=
    (hc.symm.of_dvd_left (dvd_mul_right _ _)).of_dvd_right (dvd_mul_left _ _)
  have hgcd : (r₁ * r₂).gcd (s₁ * s₂) = (r₁.gcd s₁) * (r₂.gcd s₂) := by
    rw [hss.gcd_mul, hcross₂.gcd_mul_right_cancel, hcross₁.gcd_mul_left_cancel]
  have hgg : (r₁.gcd s₁).Coprime (r₂.gcd s₂) :=
    (hrr.of_dvd_left (Nat.gcd_dvd_left _ _)).of_dvd_right (Nat.gcd_dvd_left _ _)
  simp only [gcdConvolutionSum, hgcd]
  rw [sum_divisors_coprime_mul (Nat.gcd_pos_of_pos_left _ hr₁).ne'
    (Nat.gcd_pos_of_pos_left _ hr₂).ne' hgg, sum_mul_sum]
  refine sum_congr rfl fun m hm ↦ sum_congr rfl fun n hn ↦ ?_
  have hm' := (Nat.mem_divisors.mp hm).1
  have hn' := (Nat.mem_divisors.mp hn).1
  have hmr := hm'.trans (Nat.gcd_dvd_left r₁ s₁)
  have hms := hm'.trans (Nat.gcd_dvd_right r₁ s₁)
  have hnr := hn'.trans (Nat.gcd_dvd_left r₂ s₂)
  have hns := hn'.trans (Nat.gcd_dvd_right r₂ s₂)
  rw [isMultiplicative_moebius.map_mul_of_coprime ((hgg.of_dvd_left hm').of_dvd_right hn'),
    Int.cast_mul, hu.map_mul, hv.map_mul, Nat.mul_div_mul_comm hmr hnr,
    Nat.mul_div_mul_comm hms hns,
    hconv.map_mul_of_coprime ((hrr.of_dvd_left (Nat.div_dvd_of_dvd hmr)).of_dvd_right
      (Nat.div_dvd_of_dvd hnr)),
    hconv.map_mul_of_coprime ((hss.of_dvd_left (Nat.div_dvd_of_dvd hms)).of_dvd_right
      (Nat.div_dvd_of_dvd hns))]
  ring

private theorem dirichletConvolution_prime_pow {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (hu₁ : u 1 = 1) (hv₁ : v 1 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (u * v) (p ^ k) = ∑ j ∈ range (k + 1), u p ^ j * v p ^ (k - j) := by
  have map_pow {f : ArithmeticFunction ℂ} (hf : f.IsCompletelyMultiplicative)
      (hf₁ : f 1 = 1) (e : ℕ) : f (p ^ e) = f p ^ e := by
    induction e with
    | zero => simpa using hf₁
    | succ e ih => rw [pow_succ, hf.map_mul, ih, pow_succ]
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j ↦ u i * v j),
    Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [Nat.pow_div hj' hp.pos, map_pow hu hu₁, map_pow hv hv₁]

private theorem gcdConvolutionSum_prime_pow {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative)
    (hu₁ : u 1 = 1) (hv₁ : v 1 = 1) {p : ℕ} (hp : p.Prime) (τ ξ : ℕ) :
    (u * v) (p ^ (τ + ξ)) = gcdConvolutionSum u v (p ^ τ) (p ^ ξ) := by
  cases τ with
  | zero => simp [gcdConvolutionSum, hu₁, hv₁]
  | succ τ =>
    cases ξ with
    | zero => simp [gcdConvolutionSum, hu₁, hv₁]
    | succ ξ =>
      have hgcd : (p ^ (τ + 1)).gcd (p ^ (ξ + 1)) = p ^ (min τ ξ + 1) := by
        rcases le_total τ ξ with h | h
        · rw [min_eq_left h, Nat.gcd_eq_left_iff_dvd.mpr (Nat.pow_dvd_pow p (Nat.succ_le_succ h))]
        · rw [min_eq_right h, Nat.gcd_eq_right_iff_dvd.mpr (Nat.pow_dvd_pow p (Nat.succ_le_succ h))]
      have hdiv (k : ℕ) : p ^ (k + 1) / p = p ^ k := by
        rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
      unfold gcdConvolutionSum
      -- The Möbius function kills every exponent except zero and one.
      rw [hgcd, Nat.sum_divisors_prime_pow hp, sum_range_succ', sum_range_succ']
      have hvanish : ∑ j ∈ range (min τ ξ),
          (μ (p ^ (j + 1 + 1)) : ℂ) * u (p ^ (j + 1 + 1)) * v (p ^ (j + 1 + 1)) *
            (u * v) (p ^ (τ + 1) / p ^ (j + 1 + 1)) *
            (u * v) (p ^ (ξ + 1) / p ^ (j + 1 + 1)) = 0 := by
        refine sum_eq_zero fun j _ ↦ ?_
        rw [moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
        simp
      rw [hvanish, zero_add]
      simp only [Nat.zero_add, pow_zero, pow_one, moebius_apply_one, moebius_apply_prime hp,
        Int.cast_one, Int.cast_neg, Nat.div_one, hdiv, hu₁, hv₁, one_mul]
      simp_rw [dirichletConvolution_prime_pow hu hv hu₁ hv₁ hp]
      rw [sum_pow_mul_pow_add_eq (u p) (v p) (τ + 1) (ξ + 1)]
      simp only [Nat.add_sub_cancel]
      ring

/-- **Gcd expansion of a convolution of completely multiplicative functions at a product.** Let
$u$ and $v$ be complex-valued completely multiplicative arithmetic functions, meaning
$u(mn) = u(m) u(n)$ and $v(mn) = v(m) v(n)$ for all natural numbers $m$ and $n$. Let $u * v$ be
their Dirichlet convolution and $\mu$ the Möbius function. Then for all natural numbers $r$ and
$s$,

$$(u * v)(rs) = \sum_{m \mid \gcd(r, s)} \mu(m) u(m) v(m) (u * v)(r/m) (u * v)(s/m),$$

the sum running over the positive divisors $m$ of $\gcd(r, s)$ (it is empty when $r = s = 0$).

The paper takes $r, s$ positive; the identity also holds (both sides vanish) when $r$ or $s$
is $0$, so no positivity hypothesis is imposed.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 2, Equation (17) (`integers-2024-A75-lem-2`). -/
public theorem dirichletConvolution_mul_eq_sum_gcd {u v : ArithmeticFunction ℂ}
    (hu : u.IsCompletelyMultiplicative) (hv : v.IsCompletelyMultiplicative) (r s : ℕ) :
    (u * v) (r * s) = ∑ m ∈ (Nat.gcd r s).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (r / m) * (u * v) (s / m) := by
  cases r with
  | zero => simp
  | succ r =>
    cases s with
    | zero => simp
    | succ s =>
      rcases completelyMultiplicative_eq_zero_or_map_one hu with rfl | hu₁
      · simp
      rcases completelyMultiplicative_eq_zero_or_map_one hv with rfl | hv₁
      · simp
      have hconv := (hu.isMultiplicative hu₁).mul (hv.isMultiplicative hv₁)
      suffices h : ∀ r s : ℕ, 0 < r → 0 < s → (u * v) (r * s) = gcdConvolutionSum u v r s from
        h (r + 1) (s + 1) (Nat.succ_pos _) (Nat.succ_pos _)
      intro r s hr hs
      generalize hprod : r * s = n
      induction n using Nat.strong_induction_on generalizing r s with
      | ind n ih =>
        by_cases hn : n = 1
        · have hp : r * s = 1 := hprod.trans hn
          have hr₁ : r = 1 := by
            have := Nat.le_mul_of_pos_right r hs
            omega
          have hs₁ : s = 1 := by simpa [hr₁] using hp
          subst r
          subst s
          subst n
          simp [gcdConvolutionSum, hu₁, hv₁]
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
        let τ := r.factorization p
        let ξ := s.factorization p
        let r' := r / p ^ τ
        let s' := s / p ^ ξ
        have hr' : p ^ τ * r' = r := Nat.ordProj_mul_ordCompl_eq_self r p
        have hs' : p ^ ξ * s' = s := Nat.ordProj_mul_ordCompl_eq_self s p
        have hr'₀ : 0 < r' := Nat.pos_of_ne_zero fun h ↦ hr.ne' (by simpa [h] using hr'.symm)
        have hs'₀ : 0 < s' := Nat.pos_of_ne_zero fun h ↦ hs.ne' (by simpa [h] using hs'.symm)
        have hc : (p ^ τ * p ^ ξ).Coprime (r' * s') := by
          rw [← pow_add]
          exact ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hr.ne')).mul_right
            (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hs.ne'))).pow_left _
        have hτξ : τ + ξ ≠ 0 := by
          rw [← hprod, hp.dvd_mul] at hpd
          rcases hpd with h | h
          · exact Nat.ne_of_gt (Nat.add_pos_left (hp.factorization_pos_of_dvd hr.ne' h) _)
          · exact Nat.ne_of_gt (Nat.add_pos_right _ (hp.factorization_pos_of_dvd hs.ne' h))
        have hsplit : (p ^ τ * p ^ ξ) * (r' * s') = n := by
          rw [mul_mul_mul_comm, hr', hs', hprod]
        have hlt : r' * s' < n := by
          rw [← hsplit, ← pow_add]
          simpa only [one_mul] using
            Nat.mul_lt_mul_of_pos_right (Nat.one_lt_pow hτξ hp.one_lt) (Nat.mul_pos hr'₀ hs'₀)
        calc
          (u * v) n = (u * v) (p ^ τ * p ^ ξ) * (u * v) (r' * s') := by
            rw [← hsplit, hconv.map_mul_of_coprime hc]
          _ = gcdConvolutionSum u v (p ^ τ) (p ^ ξ) * gcdConvolutionSum u v r' s' := by
            rw [← pow_add, gcdConvolutionSum_prime_pow hu hv hu₁ hv₁ hp,
              ih _ hlt r' s' hr'₀ hs'₀ rfl]
          _ = gcdConvolutionSum u v r s := by
            rw [← gcdConvolutionSum_mul hu hv hconv (pow_pos hp.pos _) hr'₀ hc, hr', hs']

end MetaMathlibExt

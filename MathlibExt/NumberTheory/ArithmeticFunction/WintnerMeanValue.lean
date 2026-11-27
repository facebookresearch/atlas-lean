/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.LinearAlgebra.LinearPMap

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private lemma wsum_id (f : ArithmeticFunction ℂ) (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, f n =
    ∑ n ∈ Finset.Icc 1 x, ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
      (((x / n : ℕ) : ℕ) : ℂ) := by
  have hζg : (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
      ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) = f := by
    rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  have h2 : ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) *
      (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) = f := by
    rw [mul_comm]; exact hζg
  have hIoc : Finset.Ioc 0 x = Finset.Icc 1 x := by ext n; simp; omega
  have hlem := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) x
  rw [hIoc] at hlem
  rw [h2] at hlem
  exact hlem

private lemma wsummable_aux (f : ArithmeticFunction ℂ)
    (hsum : Summable
      (fun n : ℕ => ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ /
        (n : ℝ))) :
    Summable (fun n : ℕ => ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n /
      (n : ℂ)) := by
  apply Summable.of_norm
  have h0 : ∀ n : ℕ, ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n /
      (n : ℂ)‖ = ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ / (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [norm_div, Complex.norm_natCast]
  exact hsum.congr (fun n => (h0 n).symm)

private lemma werr_id (g : ℕ → ℂ) (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x) :
    g n * ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ)) =
    -((g n / (n : ℂ)) * ((((x % n : ℕ) : ℕ) : ℂ) / (x : ℂ))) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have hdiv : n * (x / n) + x % n = x := Nat.div_add_mod x n
  have hcast : ((n : ℂ) * (((x / n : ℕ) : ℕ) : ℂ) + (((x % n : ℕ) : ℕ) : ℂ)) = ((x : ℕ) : ℂ) := by
    exact_mod_cast hdiv
  field_simp
  linear_combination g n * hcast

private lemma werr_norm_eq (g : ℕ → ℂ) (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x) :
    ‖g n * ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖ =
    (‖g n‖ / (n : ℝ)) * (((x % n : ℕ) : ℝ) / (x : ℝ)) := by
  rw [werr_id g n x hn hx, norm_neg, norm_mul, norm_div, norm_div,
    Complex.norm_natCast, Complex.norm_natCast, Complex.norm_natCast]

private lemma werr_le_b (g : ℕ → ℂ) (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x) :
    ‖g n * ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖ ≤ ‖g n‖ / (n : ℝ) := by
  rw [werr_norm_eq g n x hn hx]
  have hrx : ((x % n : ℕ) : ℝ) / (x : ℝ) ≤ 1 := by
    have h1 : ((x % n : ℕ) : ℝ) ≤ (x : ℝ) := by
      have hle : x % n ≤ x := by
        calc x % n ≤ n * (x / n) + x % n := Nat.le_add_left _ _
        _ = x := Nat.div_add_mod x n
      exact_mod_cast hle
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    rw [div_le_one hxpos]
    exact h1
  calc (‖g n‖ / (n : ℝ)) * (((x % n : ℕ) : ℝ) / (x : ℝ))
      ≤ (‖g n‖ / (n : ℝ)) * 1 := by gcongr
    _ = ‖g n‖ / (n : ℝ) := mul_one _

private lemma werr_le_head (g : ℕ → ℂ) (n x : ℕ) (hn : 1 ≤ n) (hx : 1 ≤ x) :
    ‖g n * ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖ ≤ ‖g n‖ / (x : ℝ) := by
  have hrn : ((x % n : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    have h1 : ((x % n : ℕ) : ℝ) < (n : ℝ) := by
      have hlt : x % n < n := Nat.mod_lt x hn
      exact_mod_cast hlt
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [div_le_one hnpos]
    exact le_of_lt h1
  have heq : (‖g n‖ / (n : ℝ)) * (((x % n : ℕ) : ℝ) / (x : ℝ)) =
      (‖g n‖ * (((x % n : ℕ) : ℝ) / (n : ℝ))) / (x : ℝ) := by
    field_simp
  rw [werr_norm_eq g n x hn hx, heq]
  calc (‖g n‖ * (((x % n : ℕ) : ℝ) / (n : ℝ))) / (x : ℝ)
      ≤ (‖g n‖ * 1) / (x : ℝ) := by gcongr
    _ = ‖g n‖ / (x : ℝ) := by rw [mul_one]

/-- **Wintner's mean-value theorem.** Let $f$ be a complex-valued arithmetic function, let $\mu$
be the Möbius function, and let $\mu * f$ be their Dirichlet convolution,
$(\mu * f)(n) = \sum_{d \mid n} \mu(d) f(n/d)$. If the series $\sum_{n \ge 1} |(\mu * f)(n)|/n$
converges, then
$$\frac{1}{x} \sum_{n=1}^{x} f(n) \to \sum_{n \ge 1} \frac{(\mu * f)(n)}{n}$$
as the integer $x$ tends to infinity.

No multiplicativity, Euler product, quantitative error term, or alternating mean is assumed or
concluded.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences
27 (2024), Article 24.8.5, mean-value definition and Theorem `Th_Wintner_gen`,
lines 292–310 (the `k = 1` case identified at lines 297–298 as Wintner's
classical theorem; the source theorem itself is Ushiroya's multivariable
generalization),
<https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex>.
-/
theorem wintner_mean_value (f : ArithmeticFunction ℂ)
    (hsum : Summable
      (fun n : ℕ => ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ /
        (n : ℝ))) :
  Filter.Tendsto (fun x : ℕ => ((x : ℂ)⁻¹) * ∑ n ∈ Finset.Icc 1 x, f n) Filter.atTop
    (nhds (∑' n : ℕ, ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n /
      (n : ℂ))) := by
  have hsumA : Summable (fun n : ℕ =>
      ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n / (n : ℂ)) :=
    wsummable_aux f hsum
  have hg0 : ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) 0 = 0 := by simp
  have ha0 :
      ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) 0 / (((0 : ℕ)) : ℂ) = 0 := by
    rw [hg0]; simp
  have hF : ∀ x : ℕ, ((x : ℂ)⁻¹) * ∑ n ∈ Finset.Icc 1 x, f n
      = ∑ n ∈ Finset.Icc 1 x,
        ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
        ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ)) := by
    intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have hsid := wsum_id f x
      rw [hsid, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
      ring
  have hPR : ∀ x : ℕ, ∑ n ∈ Finset.Icc 1 x,
        ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n / (n : ℂ)
      = ∑ n ∈ Finset.range (x + 1),
        ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n / (n : ℂ) := by
    intro x
    have hset : Finset.range (x + 1) = insert 0 (Finset.Icc 1 x) := by
      ext n; simp; omega
    rw [hset, Finset.sum_insert (by simp), ha0, zero_add]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε8 : (0 : ℝ) < ε / 8 := by linarith
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hlimB := hsum.tendsto_sum_tsum_nat
  have hlimA := hsumA.tendsto_sum_tsum_nat
  rw [Metric.tendsto_atTop] at hlimB hlimA
  obtain ⟨N₁, hN₁⟩ := hlimB (ε / 8) hε8
  obtain ⟨N₂, hN₂⟩ := hlimA (ε / 4) hε4
  set N₀ : ℕ := max N₁ N₂ with hN₀
  have hN₁₀ : N₁ ≤ N₀ := le_max_left _ _
  have hN₂₀ : N₂ ≤ N₀ := le_max_right _ _
  set C : ℝ := ∑ n ∈ Finset.Icc 1 N₀,
    ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ with hC
  have hCnn : 0 ≤ C := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (C / (ε / 4))
  set Nstar : ℕ := max N₀ (max K 1) with hNstar
  have hN₀star : N₀ ≤ Nstar := le_max_left _ _
  have hKstar : K ≤ Nstar := le_trans (le_max_left _ _) (le_max_right _ _)
  have h1star : 1 ≤ Nstar := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Nstar, fun x hx => ?_⟩
  have hxN₀ : N₀ ≤ x := le_trans hN₀star hx
  have hxK : K ≤ x := le_trans hKstar hx
  have hx1 : 1 ≤ x := le_trans h1star hx
  -- name the three quantities
  set Fx : ℂ := ((x : ℂ)⁻¹) * ∑ n ∈ Finset.Icc 1 x, f n with hFx
  set Px : ℂ := ∑ n ∈ Finset.Icc 1 x,
    ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n / (n : ℂ) with hPx
  set Sx : ℂ := ∑' n : ℕ,
    ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n / (n : ℂ) with hSx
  have hFx_eq : Fx = ∑ n ∈ Finset.Icc 1 x,
      ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
      ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ)) := hF x
  have hFP : Fx - Px = ∑ n ∈ Finset.Icc 1 x,
      ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
      ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ)) := by
    rw [hFx_eq, hPx]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_sub]
    congr 1
    rw [div_eq_mul_one_div]
  -- split the error sum
  have hsplit : Finset.Icc 1 x = Finset.Icc 1 N₀ ∪ Finset.Ioc N₀ x := by
    ext n; simp; omega
  have hdisj : Disjoint (Finset.Icc 1 N₀) (Finset.Ioc N₀ x) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp at ha1 ha2
    omega
  -- head estimate C / x < ε / 4
  have hxposR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hKposR : (0 : ℝ) < (K : ℝ) := lt_of_le_of_lt (div_nonneg hCnn (le_of_lt hε4)) hK
  have hxKR : (K : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxK
  have hheadCx : C / (x : ℝ) < ε / 4 := by
    rcases eq_or_lt_of_le hCnn with hC0 | hCpos
    · have hC0' : C = 0 := hC0.symm
      rw [hC0', zero_div]
      exact hε4
    · have h1 : C / (x : ℝ) ≤ C / (K : ℝ) :=
        div_le_div_of_nonneg_left hCpos.le hKposR hxKR
      have hK' : C < (K : ℝ) * (ε / 4) := (div_lt_iff₀ hε4).mp hK
      have h2 : C / (K : ℝ) < ε / 4 := by
        have h2' : C < (ε / 4) * (K : ℝ) := by rw [mul_comm]; exact hK'
        exact (div_lt_iff₀ hKposR).mpr h2'
      exact lt_of_le_of_lt h1 h2
  have hhead_le : ∑ n ∈ Finset.Icc 1 N₀,
        ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
        ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖
      ≤ ∑ n ∈ Finset.Icc 1 N₀,
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ / (x : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := by simp at hn; omega
    exact werr_le_head _ n x hn1 hx1
  have hhead_eq : ∑ n ∈ Finset.Icc 1 N₀,
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ / (x : ℝ))
      = C / (x : ℝ) := by
    rw [hC, Finset.sum_div]
  have hhead_lt : ∑ n ∈ Finset.Icc 1 N₀,
        ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
        ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖ < ε / 4 :=
    lt_of_le_of_lt (hhead_le.trans_eq hhead_eq) hheadCx
  -- middle (tail) estimate via real summability
  have hbnn : ∀ n : ℕ,
      0 ≤ ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ / ((n : ℕ) : ℝ) := by
    intro n; positivity
  have hle_all : ∀ s : Finset ℕ,
      ∑ i ∈ s, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))
      ≤ ∑' i, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)) := by
    intro s
    exact hsum.sum_le_tsum s (fun i _ => hbnn i)
  have hle_N0 : ∑ i ∈ Finset.range (N₀ + 1),
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))
      ≤ ∑' i, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)) :=
    hle_all _
  have hle_x : ∑ i ∈ Finset.range (x + 1),
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))
      ≤ ∑' i, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)) :=
    hle_all _
  have hdistN0 : dist
        (∑ i ∈ Finset.range (N₀ + 1),
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        (∑' i, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        < ε / 8 := by
    apply hN₁
    omega
  have htsub :
      (∑' i, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
      - (∑ i ∈ Finset.range (N₀ + 1),
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
      < ε / 8 := by
    have heq :
        (∑' i, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        - (∑ i ∈ Finset.range (N₀ + 1),
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        = dist
          (∑ i ∈ Finset.range (N₀ + 1),
            (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
          (∑' i,
            (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))) := by
      rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hle_N0)]
    rw [heq]
    exact hdistN0
  have hIco_eq : Finset.Ico (N₀ + 1) (x + 1) = Finset.Ioc N₀ x := by
    ext n; simp
  have hrange_split : ∑ i ∈ Finset.range (x + 1),
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))
      = (∑ i ∈ Finset.range (N₀ + 1),
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
      + (∑ i ∈ Finset.Ioc N₀ x,
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))) := by
    have h := Finset.sum_range_add_sum_Ico
      (fun i => ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))
      (Nat.succ_le_succ hxN₀)
    rw [hIco_eq] at h
    linarith [h]
  have hmid_le : ∑ i ∈ Finset.Ioc N₀ x,
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))
        < ε / 8 := by
    have h1 : ∑ i ∈ Finset.Ioc N₀ x,
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))
        = (∑ i ∈ Finset.range (x + 1),
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        - (∑ i ∈ Finset.range (N₀ + 1),
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))) := by
      linarith [hrange_split]
    rw [h1]
    calc (∑ i ∈ Finset.range (x + 1),
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        - (∑ i ∈ Finset.range (N₀ + 1),
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        ≤ (∑' i, (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ)))
        - (∑ i ∈ Finset.range (N₀ + 1),
          (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i‖ / ((i : ℕ) : ℝ))) :=
        sub_le_sub_right hle_x _
      _ < ε / 8 := htsub
  have hmid : ∑ n ∈ Finset.Ioc N₀ x,
        ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
        ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioc N₀ x,
        (‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n‖ / ((n : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := by
      have : N₀ < n := by simp [Finset.mem_Ioc] at hn; omega
      omega
    exact werr_le_b _ n x hn1 hx1
  have hmid_lt : ∑ n ∈ Finset.Ioc N₀ x,
        ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
        ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖ < ε / 8 :=
    lt_of_le_of_lt hmid hmid_le
  -- combine head and middle
  have hnormFP : ‖Fx - Px‖ < ε / 4 + ε / 8 := by
    rw [hFP, hsplit, Finset.sum_union hdisj]
    calc ‖(∑ n ∈ Finset.Icc 1 N₀,
          ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
          ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ)))
        + (∑ n ∈ Finset.Ioc N₀ x,
          ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
          ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ)))‖
        ≤ ‖∑ n ∈ Finset.Icc 1 N₀,
          ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
          ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖
        + ‖∑ n ∈ Finset.Ioc N₀ x,
          ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
          ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖ :=
        norm_add_le _ _
      _ ≤ (∑ n ∈ Finset.Icc 1 N₀,
          ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
          ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖)
        + (∑ n ∈ Finset.Ioc N₀ x,
          ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) n *
          ((((x / n : ℕ) : ℕ) : ℂ) / (x : ℂ) - 1 / (n : ℂ))‖) := by
        gcongr
        · exact norm_sum_le _ _
        · exact norm_sum_le _ _
      _ < ε / 4 + ε / 8 := add_lt_add hhead_lt hmid_lt
  -- complex tail
  have hdistPx : dist
      (∑ i ∈ Finset.range (x + 1),
        (((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i / ((i : ℕ) : ℂ)))
      (∑' i, (((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i / ((i : ℕ) : ℂ)))
      < ε / 4 := by
    apply hN₂
    omega
  have hnormPS : ‖Px - Sx‖ < ε / 4 := by
    have hPxr : Px = ∑ i ∈ Finset.range (x + 1),
        (((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * f) i / ((i : ℕ) : ℂ)) := hPR x
    rw [hPxr, hSx, ← dist_eq_norm]
    exact hdistPx
  -- final triangle
  have hFS : Fx - Sx = (Fx - Px) + (Px - Sx) := by ring
  have hnormFS : ‖Fx - Sx‖ < ε := by
    rw [hFS]
    calc ‖(Fx - Px) + (Px - Sx)‖ ≤ ‖Fx - Px‖ + ‖Px - Sx‖ := norm_add_le _ _
      _ < (ε / 4 + ε / 8) + ε / 4 := add_lt_add hnormFP hnormPS
      _ < ε := by linarith
  change dist ((fun x : ℕ => ((x : ℂ)⁻¹) * ∑ n ∈ Finset.Icc 1 x, f n) x) Sx < ε
  rw [dist_eq_norm]
  change ‖Fx - Sx‖ < ε
  rw [hSx]
  exact hnormFS

end MetaMathlibExt

end

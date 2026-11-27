/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.WolstenholmeBinomialExtensionNormSubTaylorLeOfNormLe

/-!
# Congruence form of the higher p-adic mean value theorem

`norm_sub_taylor_le_zpow_valuation` bounds a polynomial's Taylor remainder in an
ultrametric normed space over the p-adic numbers using the valuation of the step. It restates
the norm bound `MetaMathlibExt.norm_sub_taylor_le_of_norm_le` in terms of valuations.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 2
(`integers-2026-A32-thm-2`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Congruence form of the higher $p$-adic mean value theorem.** Let $p$ be a prime, let
$|\cdot|$ be the $p$-adic absolute value on $\mathbb{Q}_p$, and let $B$ be a normed vector space
over $\mathbb{Q}_p$ whose norm is ultrametric. Let $N$ and $m$ be natural numbers with
$1 \le m \le p$, let $f(t) = \sum_{j<N} a_j t^j$ with $a_j \in B$, let $t, h \in \mathbb{Q}_p$
with $|t| \le 1$, and let $w$ be a real number with
$\|j(j-1)\cdots(j-m+1) \, a_j\| \le p^{-w}$ for every $j < N$. Write
$$R = \Big\| f(t+h) - \sum_{q<m} \sum_{q \le j < N} \binom{j}{q} t^{j-q} h^q a_j \Big\|$$
and let $v_p(h)$ be the $p$-adic valuation of $h$, taken to be $0$ when $h = 0$. Then
$R \le p^{-(m v_p(h) + w)}$ if $m < p$ and $v_p(h) \ge 1/(p-m)$;
$R \le p^{-(p v_p(h) + w - 1)}$ if $m = p$ and $v_p(h) \ge 1/p$; and $R = 0$ if $h = 0$.

Reading a congruence modulo $p^v$ in $B$ as norm at most $p^{-v}$, the first two bounds say
$f(t+h) \equiv \sum_{q<m} f^{(q)}(t) h^q / q!$ modulo $p^{m v_p(h) + w}$ and
$p^{p v_p(h) + w - 1}$ respectively.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 2
(`integers-2026-A32-thm-2`). -/
public theorem norm_sub_taylor_le_zpow_valuation {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (w : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ (p : ℝ) ^ (-w)) :
    let R : ℝ := ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖
    (m < p → 1 / ((p : ℝ) - m) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((m : ℝ) * h.valuation + w))) ∧
      (m = p → 1 / (p : ℝ) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((p : ℝ) * h.valuation + w - 1))) ∧
      (h = 0 → R = 0) := by
  dsimp only
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hC₀ : (0 : ℝ) ≤ (p : ℝ) ^ (-w) := Real.rpow_nonneg hp0.le _
  have hnorm (hh : h ≠ 0) : ‖h‖ = (p : ℝ) ^ (-(h.valuation : ℝ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hh, ← Real.rpow_intCast, Int.cast_neg]
  have hle (hh : h ≠ 0) {r : ℝ} (hr : r ≤ h.valuation) : ‖h‖ ≤ (p : ℝ) ^ (-r) := by
    rw [hnorm hh]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (neg_le_neg hr)
  have hpow (hh : h ≠ 0) (n : ℕ) : ‖h ^ n‖ = (p : ℝ) ^ (-((n : ℝ) * h.valuation)) := by
    rw [norm_pow, hnorm hh, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    ring_nf
  refine ⟨?_, ?_, ?_⟩
  · intro hmp' hv
    have hpden : 0 < (p : ℝ) - m := sub_pos.mpr (by exact_mod_cast hmp')
    have hv' : 0 < (h.valuation : ℝ) := (one_div_pos.mpr hpden).trans_le hv
    have hh : h ≠ 0 := by
      rintro rfl
      simp at hv'
    have hm1 : ‖(m : ℚ_[p])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr
        (Nat.coprime_of_lt_prime (by omega) hmp' (Fact.out : p.Prime))
    calc _ ≤ ‖h ^ m / (m : ℚ_[p])‖ * (p : ℝ) ^ (-w) :=
          norm_sub_taylor_le_of_norm_le N m a t h _ ht hm hmp (fun _ => hle hh hv)
            (fun hpm => absurd hpm (ne_of_lt hmp')) hC₀ hC
      _ = (p : ℝ) ^ (-((m : ℝ) * h.valuation + w)) := by
        rw [norm_div, hm1, div_one, hpow hh, ← Real.rpow_add hp0]
        congr 1
        ring
  · intro hmp' hv
    subst m
    have hv' : 0 < (h.valuation : ℝ) := (one_div_pos.mpr hp0).trans_le hv
    have hh : h ≠ 0 := by
      rintro rfl
      simp at hv'
    calc _ ≤ ‖h ^ p / (p : ℚ_[p])‖ * (p : ℝ) ^ (-w) :=
          norm_sub_taylor_le_of_norm_le N p a t h _ ht hm hmp
            (fun hpp => absurd hpp (lt_irrefl _)) (fun _ => hle hh hv) hC₀ hC
      _ = (p : ℝ) ^ (-((p : ℝ) * h.valuation)) * (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-w) := by
        rw [norm_div, Padic.norm_p, hpow hh, div_inv_eq_mul, Real.rpow_one]
      _ = (p : ℝ) ^ (-((p : ℝ) * h.valuation + w - 1)) := by
        rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]
        congr 1
        ring
  · intro hh
    subst hh
    have hE := norm_sub_taylor_le_of_norm_le N m a t 0 _ ht hm hmp
      (fun _ => by rw [norm_zero]; exact Real.rpow_nonneg hp0.le _)
      (fun _ => by rw [norm_zero]; exact Real.rpow_nonneg hp0.le _) hC₀ hC
    rw [zero_pow (by omega : m ≠ 0), zero_div, norm_zero, zero_mul] at hE
    exact le_antisymm hE (norm_nonneg _)

end

end MetaMathlibExt

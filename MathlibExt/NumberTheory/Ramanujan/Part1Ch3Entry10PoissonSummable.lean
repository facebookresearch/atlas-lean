/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 10

Eventual summability of xʲφ(j)/j! for polynomially bounded φ.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10PoissonSummable

/-- Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, printed pp. 57-58 / PDF
    pp. 67-68. -/
private lemma summable_majorant_pos (C R : ℝ) (p : ℕ) (hC : 0 ≤ C) (hR : 0 < R) :
    Summable (fun n : ℕ => C * R ^ n * (n : ℝ) ^ p / (n.factorial : ℝ)) := by
  by_cases hC0 : C = 0
  · simp [hC0]
  · have hCpos : 0 < C := lt_of_le_of_ne' hC hC0
    have hpos : ∀ n : ℕ, 1 ≤ n → 0 < C * R ^ n * (n : ℝ) ^ p / (n.factorial : ℝ) := by
      intro n hn
      apply div_pos
      · apply mul_pos
        · apply mul_pos hCpos
          · exact pow_pos hR n
        · apply pow_pos
          · exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num) hn)
      · exact Nat.cast_pos.mpr (Nat.factorial_pos n)
    have hne : ∀ᶠ n : ℕ in Filter.atTop, (C * R ^ n * (n : ℝ) ^ p / (n.factorial : ℝ)) ≠ 0 := by
      apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      exact ne_of_gt (hpos n hn)
    apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) hne
    have hK_tendsto : Filter.Tendsto (fun n : ℕ => (R * 2 ^ p) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    apply squeeze_zero' (g := fun n : ℕ => (R * 2 ^ p) / (n : ℝ))
    · apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      apply div_nonneg (norm_nonneg _) (norm_nonneg _)
    · apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num) hn)
      have hfn_nonneg : 0 ≤ C * R ^ n * (n : ℝ) ^ p / (n.factorial : ℝ) :=
        le_of_lt (hpos n hn)
      have hfn1_nonneg : 0 ≤ C * R ^ (n + 1) * (((n + 1 : ℕ)) : ℝ) ^ p / (((n + 1 : ℕ).factorial : ℝ)) := by
        have h1 : 1 ≤ n + 1 := by omega
        exact le_of_lt (hpos (n + 1) h1)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hfn1_nonneg,
        abs_of_nonneg hfn_nonneg]
      have hpow_le : (((n + 1 : ℕ) : ℝ)) ^ p ≤ 2 ^ p * (n : ℝ) ^ p := by
        have hle : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
          push_cast
          have h1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
          linarith
        calc (((n + 1 : ℕ) : ℝ)) ^ p ≤ (2 * (n : ℝ)) ^ p :=
              pow_le_pow_left₀ (by positivity) hle p
          _ = 2 ^ p * (n : ℝ) ^ p := by ring
      have hfact : (((n + 1 : ℕ).factorial : ℝ)) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfact, pow_succ]
      field_simp
      have hA : ((((n + 1 : ℕ)) : ℝ)) ^ p * (n : ℝ) ≤ (2 ^ p * (n : ℝ) ^ p) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hpow_le (le_of_lt hn_pos)
      have hB : (2 ^ p * (n : ℝ) ^ p) * (n : ℝ) ≤ (2 ^ p * (n : ℝ) ^ p) * ((n : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have hCeq : (2 ^ p * (n : ℝ) ^ p) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * (n : ℝ) ^ p * 2 ^ p := by ring
      linarith
    · exact hK_tendsto

private lemma summable_majorant (C R : ℝ) (p : ℕ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    Summable (fun n : ℕ => C * R ^ n * (n : ℝ) ^ p / (n.factorial : ℝ)) := by
  by_cases hR0 : R = 0
  · subst hR0
    have h1 : Summable (fun n : ℕ => C * (1 : ℝ) ^ n * (n : ℝ) ^ p / (n.factorial : ℝ)) :=
      summable_majorant_pos C 1 p hC (by norm_num)
    apply Summable.of_nonneg_of_le _ _ h1
    · intro n
      apply div_nonneg
      · apply mul_nonneg
        · apply mul_nonneg hC
          · exact pow_nonneg (le_refl 0) n
        · exact pow_nonneg (Nat.cast_nonneg n) p
      · exact Nat.cast_nonneg _
    · intro n
      have h01 : (0 : ℝ) ^ n ≤ (1 : ℝ) ^ n :=
        pow_le_pow_left₀ (le_refl 0) (by norm_num) n
      gcongr
  · have hRpos : 0 < R := lt_of_le_of_ne' hR hR0
    exact summable_majorant_pos C R p hC hRpos

/-- **Eventual summability of the series in Entry 10.** Let $\varphi : \mathbb{R} \to \mathbb{C}$
be polynomially bounded at infinity, that is, there are a real number $C \ge 0$ and a natural
number $p$ such that $|\varphi(x)| \le C x^p$ for all sufficiently large real $x$. Let $F$ be a
finite set of natural numbers. Then for all sufficiently large real $x$, the family indexed by
the natural numbers $j$ whose $j$-th term is $0$ for $j \in F$ and $x^j \varphi(j) / j!$ for
$j \notin F$ is summable.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, printed pp. 57-58 / PDF
    pp. 67-68.
Proves `Wanted` entry `ramanujan_part1_ch3_entry10_poisson_summable`.
-/
theorem ramanujan_part1_ch3_entry10_poisson_summable
    (φ : ℝ → ℂ) (F : Finset ℕ)
    (hφ : ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ᶠ (x : ℝ) in Filter.atTop, ‖φ x‖ ≤ C * x ^ p) :
    ∀ᶠ (x : ℝ) in Filter.atTop,
      Summable (fun j : ℕ => if j ∈ F then 0 else ((x : ℂ) ^ j * φ (j : ℝ) / (Nat.factorial j : ℂ))) := by
  obtain ⟨C, p, hC, hφ⟩ := hφ
  rw [Filter.eventually_atTop] at hφ
  obtain ⟨N0, hN0⟩ := hφ
  apply Filter.Eventually.of_forall
  intro x
  have hR : 0 ≤ |x| := abs_nonneg x
  have hsum : Summable (fun n : ℕ => C * |x| ^ n * (n : ℝ) ^ p / (n.factorial : ℝ)) :=
    summable_majorant C |x| p hC hR
  apply Summable.of_norm_bounded_eventually hsum
  rw [Nat.cofinite_eq_atTop]
  rw [Filter.eventually_atTop]
  refine ⟨max (F.sup id + 1) (Nat.ceil N0), fun j hj => ?_⟩
  have hj_sup : F.sup id + 1 ≤ j := le_trans (Nat.le_max_left _ _) hj
  have hj_ceil : Nat.ceil N0 ≤ j := le_trans (Nat.le_max_right _ _) hj
  have hjF : j ∉ F := by
    intro hjmem
    have hle : id j ≤ F.sup id := Finset.le_sup hjmem
    simp [id] at hle
    omega
  have hjN0 : N0 ≤ (j : ℝ) := by
    calc N0 ≤ ((Nat.ceil N0 : ℕ) : ℝ) := Nat.le_ceil N0
      _ ≤ (j : ℝ) := Nat.cast_le.mpr hj_ceil
  have hif : (if j ∈ F then (0 : ℂ) else ((x : ℂ) ^ j * φ (j : ℝ) / (Nat.factorial j : ℂ)))
      = ((x : ℂ) ^ j * φ (j : ℝ) / (Nat.factorial j : ℂ)) := by simp [hjF]
  rw [hif]
  have hφj : ‖φ (j : ℝ)‖ ≤ C * (j : ℝ) ^ p := hN0 _ hjN0
  have hnorm_eq : ‖((x : ℂ) ^ j * φ (j : ℝ) / (Nat.factorial j : ℂ))‖
      = |x| ^ j * ‖φ (j : ℝ)‖ / (j.factorial : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
  rw [hnorm_eq]
  have hfact_pos : 0 < ((j.factorial : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
  have hRpow_nonneg : 0 ≤ |x| ^ j := pow_nonneg (abs_nonneg x) j
  have hCjp_nonneg : 0 ≤ C * (j : ℝ) ^ p := mul_nonneg hC (pow_nonneg (Nat.cast_nonneg j) p)
  calc |x| ^ j * ‖φ (j : ℝ)‖ / (j.factorial : ℝ)
      = (|x| ^ j / (j.factorial : ℝ)) * ‖φ (j : ℝ)‖ := by ring
    _ ≤ (|x| ^ j / (j.factorial : ℝ)) * (C * (j : ℝ) ^ p) := by
        apply mul_le_mul_of_nonneg_left hφj (by positivity)
    _ = C * |x| ^ j * (j : ℝ) ^ p / (j.factorial : ℝ) := by ring

end Entry10PoissonSummable
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3

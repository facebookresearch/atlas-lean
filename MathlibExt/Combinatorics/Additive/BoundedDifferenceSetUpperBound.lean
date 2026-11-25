/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.GDifferenceBases
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An asymptotic upper bound for sets of bounded difference multiplicity
-/

namespace MetaMathlibExt

open Filter Finset
open scoped BigOperators

private theorem sum_ones_of_subset {S B : Finset ℤ} (h : B ⊆ S) :
    (∑ x ∈ S, (if x ∈ B then 1 else 0 : ℝ)) = B.card := by
  rw [Finset.sum_boole, show S.filter (· ∈ B) = B by
    ext x
    exact Finset.mem_filter.trans ⟨And.right, fun hx => ⟨h hx, hx⟩⟩]

-- Count the incidences of the translates A + i and apply Cauchy–Schwarz in their union.
private theorem card_sq_le_of_bounded_differences {g n : ℕ} (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc 1 (n : ℤ)) (hrep : ∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g)
    (m : ℕ) (hm : 0 < m) :
    (A.card : ℝ) ^ 2 ≤ ((n : ℝ) + m) * ((A.card : ℝ) / m + g) := by
  let B (i : ℕ) := A.map (⟨(· + (i : ℤ)), fun _ _ => add_right_cancel⟩ : ℤ ↪ ℤ)
  let S := Finset.Icc (1 : ℤ) ((n : ℤ) + m)
  let w (i : ℕ) (x : ℤ) : ℝ := if x ∈ B i then 1 else 0
  let r (x : ℤ) := ∑ i ∈ range m, w i x
  have hsub {i : ℕ} (hi : i ∈ range m) : B i ⊆ S := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    have ha' := Finset.mem_Icc.mp (hA ha)
    have hi' := Finset.mem_range.mp hi
    apply Finset.mem_Icc.mpr
    change 1 ≤ a + (i : ℤ) ∧ a + (i : ℤ) ≤ (n : ℤ) + m
    omega
  have hsum : ∑ x ∈ S, r x = (m : ℝ) * A.card := by
    dsimp only [r]
    rw [Finset.sum_comm]
    calc
      ∑ i ∈ range m, ∑ x ∈ S, w i x = ∑ _i ∈ range m, (A.card : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [sum_ones_of_subset (hsub hi)]
        simp [B]
      _ = _ := by simp
  have hoverlap {i j : ℕ} (hij : i ≠ j) : (B i ∩ B j).card ≤ g := by
    refine le_trans ?_ (hrep ((j : ℤ) - i) (by omega))
    apply Finset.card_le_card_of_injOn (fun x : ℤ => (x - i, x - j))
    · intro x hx
      obtain ⟨hi, hj⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp hx)
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨b, hb, hb'⟩ := Finset.mem_map.mp hj
      change b + (j : ℤ) = a + (i : ℤ) at hb'
      change (a + (i : ℤ) - i, a + (i : ℤ) - j) ∈
        ((A ×ˢ A).filter fun p => p.1 - p.2 = (j : ℤ) - i : Finset (ℤ × ℤ))
      have he : a + (i : ℤ) - j = b := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by simpa using ha, ?_⟩, by omega⟩
      rwa [he]
    · intro x _ y _ he
      exact sub_left_injective (congrArg Prod.fst he)
  have hpair {i j : ℕ} (hi : i ∈ range m) :
      ∑ x ∈ S, w i x * w j x ≤ (if j = i then (A.card : ℝ) else 0) + g := by
    have he : ∑ x ∈ S, w i x * w j x = ((B i ∩ B j).card : ℝ) := by
      rw [← sum_ones_of_subset (Finset.inter_subset_left.trans (hsub hi) : B i ∩ B j ⊆ S)]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ B i <;> by_cases hy : x ∈ B j <;> simp [w, hx, hy]
    rw [he]
    by_cases hij : j = i
    · subst j
      simp [B]
    · rw [ite_eq_right hij, zero_add]
      exact_mod_cast hoverlap (Ne.symm hij)
  have hsquares : ∑ x ∈ S, r x ^ 2 ≤ (m : ℝ) * ((A.card : ℝ) + m * g) := by
    calc
      ∑ x ∈ S, r x ^ 2 = ∑ i ∈ range m, ∑ j ∈ range m, ∑ x ∈ S, w i x * w j x := by
        simp only [r, pow_two, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_congr rfl fun x _ => mul_comm (w j x) (w i x)
      _ ≤ ∑ i ∈ range m, ∑ j ∈ range m, ((if j = i then (A.card : ℝ) else 0) + g) :=
        Finset.sum_le_sum fun _ hi => Finset.sum_le_sum fun _ _ => hpair hi
      _ = _ := by
        calc
          _ = ∑ _i ∈ range m, ((A.card : ℝ) + m * g) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.sum_add_distrib, hi]
          _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hS : (S.card : ℝ) = (n : ℝ) + m := by
    have hcard : S.card = n + m := by
      dsimp [S]
      rw [← Int.natCast_add, Int.card_Icc]
      omega
    exact_mod_cast hcard
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) r
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, hS] at hcs
  have hb := hcs.trans (mul_le_mul_of_nonneg_left hsquares (by positivity :
    0 ≤ (n : ℝ) + m))
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply (le_of_mul_le_mul_right ?_ (show 0 < (m : ℝ) ^ 2 by positivity))
  calc
    (A.card : ℝ) ^ 2 * (m : ℝ) ^ 2 = ((m : ℝ) * A.card) ^ 2 := by ring
    _ ≤ ((n : ℝ) + m) * (m * ((A.card : ℝ) + m * g)) := hb
    _ = ((n : ℝ) + m) * ((A.card : ℝ) / m + g) * (m : ℝ) ^ 2 := by
      field_simp

open Filter in
/-- **Upper bound for sets with bounded difference multiplicities.** For natural numbers $g$ and
$n$, let $\alpha_g(n)$ be the largest size of a set $A \subseteq \{1, \dots, n\}$ such that every
nonzero integer $x$ is the difference $a - a'$ of at most $g$ ordered pairs
$(a, a') \in A \times A$. If $g \ge 1$, then for every real $\varepsilon > 0$ we have
$\alpha_g(n) \le (1 + \varepsilon)\sqrt{gn}$ for all sufficiently large $n$; that is,
$\alpha_g(n) \le (1 + o(1))\sqrt{gn}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 1 (`integers-2025-A77-prop-1`). -/
public theorem boundedDiffSetNumber_le_one_add_mul_sqrt (g : ℕ) (hg : 0 < g) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (boundedDiffSetNumber g n : ℝ) ≤ (1 + ε) * Real.sqrt (g * n) := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨d, hd⟩ := exists_nat_gt (2 / δ)
  have hd' : (0 : ℝ) < d := (by positivity : 0 ≤ 2 / δ).trans_lt hd
  have hdpos : 0 < d := by exact_mod_cast hd'
  have hdδ : 2 ≤ δ * (d : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hd.le
  obtain ⟨N, hN⟩ := exists_nat_gt ((((d : ℝ) + 1) / δ) ^ 2)
  filter_upwards [eventually_ge_atTop d, eventually_ge_atTop N] with n hn hNn
  let admissible : Set ℕ := {k | ∃ A : Finset ℤ, A ⊆ Icc 1 (n : ℤ) ∧ A.card = k ∧
    ∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g}
  have hne : admissible.Nonempty := ⟨0, ∅, by simp, by simp, by simp [subRepCount]⟩
  have hbdd : BddAbove admissible := ⟨n, by
    rintro _ ⟨A, hA, rfl, -⟩
    simpa using Finset.card_le_card hA⟩
  obtain ⟨A, hA, hcard, hrep⟩ := Nat.sSup_mem hne hbdd
  change A.card = boundedDiffSetNumber g n at hcard
  rw [← hcard]
  -- Use about n/d translates: their support increases by at most δ * n, and
  -- the diagonal overlap contributes a term at most (d + 1) times the cardinality.
  let m := n / d + 1
  have hm : 0 < m := Nat.succ_pos _
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hdm : (n : ℝ) ≤ (d : ℝ) * m := by
    exact_mod_cast (Nat.lt_mul_div_succ n hdpos).le
  have hmd : (m : ℝ) * d ≤ (n : ℝ) + d := by
    have h : ((n / d : ℕ) : ℝ) * d ≤ (n : ℝ) := by
      exact_mod_cast ((mul_comm _ _).trans_le (Nat.mul_div_le n d) : (n / d) * d ≤ n)
    simpa only [m, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using add_le_add_left h (d : ℝ)
  have hn' : (d : ℝ) ≤ n := by exact_mod_cast hn
  have hmδ : (m : ℝ) ≤ δ * n := by
    apply le_of_mul_le_mul_right ?_ hd'
    calc
      (m : ℝ) * d ≤ (n : ℝ) + d := hmd
      _ ≤ 2 * (n : ℝ) := by linarith
      _ ≤ (δ * d) * n := mul_le_mul_of_nonneg_right hdδ (by positivity)
      _ = δ * (n : ℝ) * d := by ring
  have hratio : ((n : ℝ) + m) / m ≤ (d : ℝ) + 1 := by
    apply (div_le_iff₀ hm').mpr
    linarith only [hdm, show ((d : ℝ) + 1) * m = d * m + m by ring]
  let k : ℝ := A.card
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hk2 : k ^ 2 ≤ ((d : ℝ) + 1) * k + ((n : ℝ) + m) * g := calc
    _ ≤ ((n : ℝ) + m) * (k / m + g) := card_sq_le_of_bounded_differences A hA hrep m hm
    _ = (((n : ℝ) + m) / m) * k + ((n : ℝ) + m) * g := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right hratio hk) _
  let x := Real.sqrt ((g : ℝ) * n)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = (g : ℝ) * n := Real.sq_sqrt (by positivity)
  let y := (1 + δ) * x
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hmain : ((n : ℝ) + m) * g ≤ y ^ 2 := calc
    _ ≤ ((n : ℝ) + δ * n) * g :=
      mul_le_mul_of_nonneg_right (add_le_add_right hmδ _) (by positivity)
    _ = (1 + δ) * ((g : ℝ) * n) := by ring
    _ ≤ y ^ 2 := by
      change _ ≤ ((1 + δ) * x) ^ 2
      rw [mul_pow, hx2]
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg δ]) (by positivity)
  have hky : k ≤ y + ((d : ℝ) + 1) := by
    by_contra! h
    have hlt := mul_lt_mul_of_pos_right (show y < k - ((d : ℝ) + 1) by linarith)
      (show 0 < k by linarith [hd', hy])
    have hle := mul_le_mul_of_nonneg_left (show y ≤ k by linarith [hd']) hy
    nlinarith only [hk2, hmain, hlt, hle]
  have hgn : (n : ℝ) ≤ (g : ℝ) * n :=
    le_mul_of_one_le_left (by positivity) (by exact_mod_cast hg)
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hbudget : (d : ℝ) + 1 ≤ δ * x := by
    rw [mul_comm δ x, ← div_le_iff₀ hδ]
    exact (Real.le_sqrt (by positivity) (by positivity)).mpr (hN.le.trans (hNn'.trans hgn))
  change k ≤ (1 + ε) * x
  calc
    k ≤ y + ((d : ℝ) + 1) := hky
    _ ≤ y + δ * x := add_le_add_right hbudget y
    _ = (1 + ε) * x := by dsimp [y, δ]; ring

end MetaMathlibExt
